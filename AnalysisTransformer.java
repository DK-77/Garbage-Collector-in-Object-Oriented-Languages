import java.util.*;

import jasmin.sym;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JDynamicInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;
// import PTG;

class PTG_Node{
    String name;
    Map<String,PTG_Node> fields;

    public PTG_Node(String str){
        name = str;
        fields = new HashMap<>();
    }
}

class PTG {

    List<PTG_Node> nodes;
    Map<PTG_Node,List<PTG_Node>> edges;

    public PTG(){
        nodes = new ArrayList<>();
        edges = new HashMap<>();
    }

    // Search a node in Graph
    public PTG_Node findNode(List<PTG_Node> l, String str){
        
        if(l.isEmpty()){
            return null;
        }

        for(PTG_Node n: l){
            if(n.name.equals(str)) return n;
        }
        return null;
    }
    
    // Add and a node with no edges in grapgh
    public void addNode(PTG_Node n){
        PTG_Node t = findNode(nodes, n.name);
        if(t == null){
            nodes.add(n);
        }
    }

    // Remove a Node as well as its associated Edges
    public void removeNode(String str){
        
        // Removing all edges from the Node
        PTG_Node rm_node = findNode(nodes, str);
        edges.remove(rm_node);

        //Removing all edges to the Node
        rm_node = findNode(nodes, str);
        List<PTG_Node> from_nodes = new ArrayList<>();
        for(Map.Entry<PTG_Node,List<PTG_Node>> m: edges.entrySet()){
            if(m.getValue().contains(rm_node)) from_nodes.add(m.getKey());
        }
        for(PTG_Node n: from_nodes){
            // System.out.println(n.name);
            edges.remove(n);
        }

        // Removing Nodes from list of Node
        nodes.remove(rm_node);
    }

    // find if any rhs is pointing to an Object node
    public List<PTG_Node> findObject(String str){
        for(Map.Entry<PTG_Node,List<PTG_Node>> m: edges.entrySet()){
            PTG_Node key = m.getKey();
            if(key.name.equals(str)){
                List<PTG_Node> values = m.getValue();
                return values;
            }
        }
        return null;
    }

    //Get Object pointed to by the field
    public PTG_Node findField(PTG_Node o, String field){
        
        for(Map.Entry<String,PTG_Node> e: o.fields.entrySet()){
            String k = e.getKey();
            if(k.equals(field)){
                return e.getValue();
            }
        }
        
        return null;
    }

    //Add and edge in the graph
    public void addEdge(PTG_Node from, String field, PTG_Node to){
        
        PTG_Node f,t;
        f = findNode(nodes, from.name);
        t = findNode(nodes, to.name);
        
        
        if(f == null && t == null){
            if(field != null) from.fields.put(field, to);
            edges.computeIfAbsent(from, k -> new ArrayList<>()).add(to);
            nodes.add(from);
            nodes.add(to);
        }
        else if(f != null && t == null){
            if(field != null) f.fields.put(field, to);
            edges.computeIfAbsent(f, k -> new ArrayList<>()).add(to);
            nodes.add(to);
        }
        else if(f == null && t != null){
            if(field != null) from.fields.put(field, t);
            edges.computeIfAbsent(from, k -> new ArrayList<>()).add(t);
            nodes.add(from);
        }
        else{
            if(field != null) f.fields.put(field, t);
            edges.computeIfAbsent(f, k -> new ArrayList<>()).add(t);
        }
    }
     
    // Print the Graph
    public void printGraph(){
    
        if(nodes.isEmpty()){
            System.out.println("Empty Graph!");
            return;
        }
        System.out.println("Nodes");
        for(PTG_Node n: nodes){
            System.out.print(n.name+"   ");
        }
        System.out.println("\n");
        if(edges.isEmpty()){
            System.out.println("No Edges present!");
            return;
        }
        System.out.println("Edges");
        for(Map.Entry<PTG_Node,List<PTG_Node>> m: edges.entrySet()){
            PTG_Node key = m.getKey();
            List<PTG_Node> val = m.getValue();
            for(PTG_Node n: val){
                System.out.println(key.name+"---------->"+n.name+"                   "+key+"----------->"+n);
            }
        }
        
    }

}

class processCFGReq {
    PTG preceedingPTG;
    Map<PTG,Map<Integer,String>> child;
    Map<String,Integer> ref_last_used;
    Map<Integer,String> params_to_me;
    SootMethod method;
    Integer begin;
    Integer end;
    TreeSet<String> gcedObjects;

    public processCFGReq(PTG preceedingPTG,Map<PTG,Map<Integer,String>> child,Map<String,Integer> ref_last_used,Map<Integer,String> params_to_me, SootMethod method, Integer begin, Integer end){
        this.preceedingPTG = preceedingPTG;
        this.child = child;
        this.ref_last_used = ref_last_used;
        this.params_to_me = params_to_me;
        this.method = method;
        this.begin = begin;
        this.end = end;
    }
}


public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    static Stack<SootMethod> stk = new Stack<>();
    static Map<PTG,Map<Integer,String>> pointsTo_param = null;
    static processCFGReq args = new processCFGReq(null, null, null, null, null, -7, -7);
    static TreeMap<String,TreeSet<String>> globalGced = new TreeMap<>();

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new HashSet <>();
        cg = Scene.v().getCallGraph();
        // Get the main method
        SootMethod mainMethod = Scene.v().getMainMethod();
        // System.out.println(mainMethod);
        // Get the list of methods reachable from the main method
        // Note: This can be done bottom up manner as well. Might be easier to model.
        // queue.offer(pointsTo_param);
        // System.out.println("here");
        processInOrder(mainMethod);
        // getlistofMethods(mainMethod, methods);

        // for (SootMethod m : methods) {
        //     // System.out.println("method: "+m.getName());
        //     processCFG(m);
        // }
    }

    protected static processCFGReq processCFG(processCFGReq  reqs) {
        // if(method.isConstructor()) { return; }
        Body body = reqs.method.getActiveBody();
        
        // Get the callgraph    
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body
        PatchingChain<Unit> units = body.getUnits();
        
        PTG ptg = null;
        if(reqs.preceedingPTG != null) ptg = reqs.preceedingPTG;
        else ptg = new PTG(); 

        PTG mPTG = null;
        Map<String,Integer> ref_last_used;
        if(reqs.ref_last_used != null) ref_last_used = reqs.ref_last_used;
        else ref_last_used = new HashMap<>();

        Map<Integer,String> params_to_child = new HashMap<>();
        
        Map<Integer,String> params_to_me;
        if(reqs.params_to_me != null) params_to_me = reqs.params_to_me;
        else params_to_me = new HashMap<>();
        
        Map<PTG,Map<Integer,String>> ptg_params = new HashMap<>();
        
        TreeSet<String> collObjects ;
        if(reqs.gcedObjects != null) collObjects = reqs.gcedObjects;
        else collObjects = new TreeSet<>();

        String retVar = null;
        Integer call_line_number = null; 
        Integer stmt_last_processed = 0;
        Boolean callPrint = false;
        Boolean isparam = false;
        // List<PTG_Node> l1;
        // PTG_Node node = new PTG_Node();
        String mthd = body.getMethod().getName();
        // System.out.println("\n----- " + body.getMethod().getName() + "-----");
        for (Unit u : units) {
            
            if( reqs.begin != -7 )
                if(u.getJavaSourceStartLineNumber() < reqs.begin) continue;
                else if(u.getJavaSourceStartLineNumber() > reqs.end) break;
            
            String ln = String.valueOf(u.getJavaSourceStartLineNumber());
            // System.out.println("Stmt: "+u+" at line: "+ ln);
            
            if (u instanceof AssignStmt) {
                
                AssignStmt assignStmt = (AssignStmt) u;
                Value rhs = assignStmt.getRightOp();
                
                if (rhs instanceof InvokeExpr || rhs instanceof JStaticInvokeExpr || rhs instanceof JVirtualInvokeExpr ) {
                    // System.out.println("Found an InvokeExpr with a LHS: " + assignStmt);
                    Value lhs = assignStmt.getLeftOp();
                    retVar = mthd+"_"+lhs.toString();
                    // System.out.println("ret value is :"+ retVar);
                    ref_last_used.put(retVar,Integer.valueOf(ln));
                    // System.out.println("The LHS of the InvokeExpr is: " + lhs);                   
                }
                InvokeExpr expr = null;
                if(rhs instanceof JStaticInvokeExpr || rhs instanceof JVirtualInvokeExpr){
                    expr = ((InvokeExpr)rhs);
                    // System.out.println(expr.getMethod().getSignature());
                    if(expr instanceof JVirtualInvokeExpr && ((JVirtualInvokeExpr)expr).getMethodRef().getDeclaringClass().getName().contains("java")){
                        int argCount = expr.getArgCount();
                        for(int i=0;i<argCount;i++){    
                            if(expr.getArg(i) instanceof Local){
                                ref_last_used.put(mthd+"_"+expr.getArg(i).toString(),Integer.valueOf(ln));
                            }
                        }
                    }
                    else{
                        if(expr instanceof JVirtualInvokeExpr){
                            ref_last_used.put(mthd+"_"+((JVirtualInvokeExpr)expr).getBase().toString(),Integer.valueOf(ln));
                        }
                        if(expr instanceof JVirtualInvokeExpr || expr instanceof JStaticInvokeExpr){
                            // if(expr instanceof JStaticInvokeExpr)     System.out.println(expr.getMethod().getSignature());
                            int argCount = expr.getArgCount();
                            // Integer flag = 0;
                            for(int i=0;i<argCount;i++){
                                params_to_child.put(i, mthd+"_"+expr.getArg(i).toString());
                                ref_last_used.put(mthd+"_"+expr.getArg(i).toString(),Integer.valueOf(ln));
                                // System.out.println("string  "+mthd+"_"+expr.getArg(i).toString()+"   last used  "+Integer.valueOf(ln));
                                // flag = 1;
                            }
                            // System.out.println("stmt is -------> "+ u);
                            call_line_number = u.getJavaSourceStartLineNumber();
                        }
                    }
                }
            }

            if (u instanceof JAssignStmt) {
                JAssignStmt stmt = (JAssignStmt) u;
                Value lhs = stmt.getLeftOp();
                Value rhs = stmt.getRightOp();
                boolean rhsfr = rhs instanceof InstanceFieldRef;
                boolean lhsfr = lhs instanceof InstanceFieldRef;
                String ty = null;
                if(rhs instanceof JNewExpr){
                    ty = ((JNewExpr)rhs).getBaseType().toString();
                    ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()), null , new PTG_Node(ty+"#"+"Object_"+ln));
                    
                    ref_last_used.put(mthd+"_"+lhs.toString(),Integer.valueOf(ln));
                }

                if(lhs instanceof Local && rhs instanceof Local){
                    PTG_Node n = findObj(ptg, mthd, rhs);
                    if(n!=null) ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()), null , n);
                    
                    ref_last_used.put(mthd+"_"+lhs.toString(),Integer.valueOf(ln));
                    ref_last_used.put(mthd+"_"+rhs.toString(),Integer.valueOf(ln));
                }

                if(rhsfr && !lhsfr){
                    
                    PTG_Node t1 = new PTG_Node("null");
                    Value base = ((InstanceFieldRef)rhs).getBase();
                    for(Map.Entry<Integer,String> m: params_to_me.entrySet()){
                        if(m.getValue().equals(mthd+"_"+base.toString())){
                            isparam = true;
                            break;
                        } 
                    }

                    PTG_Node t = findObj(ptg, mthd, base);
                    if(isparam){
                        String s = ((InstanceFieldRef)rhs).getField().getName();
                        if(t != null) t1 = ptg.findField(t,s);
                        if(t1 == null){ 
                            PTG_Node temp1 = new PTG_Node(t.name+"_"+s);
                            ptg.addEdge( t, s, temp1);
                            if(lhs.toString().equals(base.toString())) { ptg.removeNode(mthd+"_"+lhs.toString()); ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,temp1); }//perform strong update 
                            else ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,temp1);
                        }
                        else{
                            if(lhs.toString().equals(base.toString())) { ptg.removeNode(mthd+"_"+lhs.toString()); ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,t1); }// perform strong update        
                            else ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,t1);
                        }
                    }
                    else{
                        // PTG_Node t = findObj(ptg, mthd, base);
                        if(t != null) t1 = ptg.findField(t,((InstanceFieldRef)rhs).getField().getName());
                        if(t1 == null) { 
                            if(lhs.toString().equals(base.toString())) { ptg.removeNode(mthd+"_"+lhs.toString());  ptg.addNode(new PTG_Node(mthd+"_"+lhs.toString())); }// perform strong update        
                            else ptg.addNode(new PTG_Node(mthd+"_"+lhs.toString()));
                        }
                        else {
                            if(lhs.toString().equals(base.toString())) { ptg.removeNode(mthd+"_"+lhs.toString()); ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,t1); }//perform strong update 
                            else ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()),null,t1);
                        }
                    }

                    ref_last_used.put(mthd+"_"+lhs.toString(),Integer.valueOf(ln));
                    ref_last_used.put(mthd+"_"+base.toString(),Integer.valueOf(ln));
                }

                if(lhsfr && !rhsfr){
                    if(rhs instanceof JNewExpr){
                        // This does not happen in jimple
                        // System.out.println("r.f = new Node happened");
                    }
                    else if(rhs instanceof Local){
                        
                        PTG_Node t = findObj(ptg, mthd, rhs);
                        Value base = ((InstanceFieldRef)lhs).getBase();
                        PTG_Node t2 = findObj(ptg, mthd, base);

                        if(t != null) 
                            if(t2!=null) // no need to ckeck this when we include dummy objects
                                ptg.addEdge(t2,((InstanceFieldRef)lhs).getField().getName(),t);
                        
                        ref_last_used.put(mthd+"_"+base.toString(),Integer.valueOf(ln));
                        ref_last_used.put(mthd+"_"+rhs.toString(),Integer.valueOf(ln));
                    }
                }

                if(lhsfr && rhsfr){
                    // Not tested
                    
                    Value basel = ((InstanceFieldRef)lhs).getBase();
                    Value baser = ((InstanceFieldRef)rhs).getBase();
                    PTG_Node t1 = findObj(ptg, mthd, basel);
                    PTG_Node t2 = findObj(ptg, mthd, baser);
                    PTG_Node t3 = new PTG_Node("null");

                    if(t2!=null)  // No need to check after dummy
                        t3 = ptg.findField(t2, ((InstanceFieldRef)rhs).getField().getName());
                    if(t1!=null) // No need to check after dummy
                        if(t2!=null) // No need to check after dummy
                            if(t3!=null)
                                ptg.addEdge(t1, ((InstanceFieldRef)lhs).getField().getName(), t3);

                    ref_last_used.put(mthd+"_"+basel.toString(),Integer.valueOf(ln));
                    ref_last_used.put(mthd+"_"+baser.toString(),Integer.valueOf(ln));
                }
            }

            if(u instanceof IdentityStmt){

                IdentityStmt identityStmt = (IdentityStmt) u;
                Value lhs = identityStmt.getLeftOp();
                Value rhs = identityStmt.getRightOp();

                if(lhs instanceof Local && rhs instanceof ParameterRef){
                    ptg.addEdge(new PTG_Node(mthd+"_"+lhs.toString()), null , new PTG_Node(mthd+"_"+lhs.toString()+"_Dummy_Object"));
                    
                    params_to_me.put(((ParameterRef)rhs).getIndex(), mthd+"_"+lhs.toString());
                    
                }

                ref_last_used.put(mthd+"_"+lhs.toString(),Integer.valueOf(ln));
                // Here, the case when rhs is instance of @this is not handled
            }

            if(u instanceof JReturnStmt){
                
                // System.out.println("Stmt: "+u+" at line: "+u.getJavaSourceStartLineNumber());
                JReturnStmt returnStmt = (JReturnStmt) u;
                Value returnValue = returnStmt.getOp();
                PTG_Node t1 = new PTG_Node("null");
                ref_last_used.put(mthd+"_return", Integer.valueOf(ln));

                if(returnValue instanceof Local){
                    
                    t1 = findObj(ptg, mthd, returnValue);
                    if(t1 != null)// No need to check after dummy
                        ptg.addEdge(new PTG_Node(mthd+"_return"), null, t1);
                    
                    ref_last_used.put(mthd+"_"+returnValue.toString(),Integer.valueOf(ln));

                }
                else if(returnValue instanceof InstanceFieldRef){
                    // Not tested
                    Value base = ((InstanceFieldRef)returnValue).getBase();
                    t1 = findObj(ptg, mthd, base);
                    PTG_Node t2 = null;
                    if(t1 != null)
                        t2 = ptg.findField(t1, ((InstanceFieldRef)returnValue).getField().getName());
                    if(t2 != null)
                        ptg.addEdge(new PTG_Node(mthd+"_return"), null, t2);

                    ref_last_used.put(mthd+"_"+base.toString(),Integer.valueOf(ln));
                }
                
            }



            if(u instanceof JInvokeStmt){
                
                JInvokeStmt invokeStmt = (JInvokeStmt) u;
                InvokeExpr expr = invokeStmt.getInvokeExpr();
                
                // System.out.println(expr.getMethod().getSignature());
                if(expr instanceof JVirtualInvokeExpr && ((JVirtualInvokeExpr)expr).getMethodRef().getDeclaringClass().getName().contains("java")){
                    int argCount = expr.getArgCount();
                    for(int i=0;i<argCount;i++){    
                        if(expr.getArg(i) instanceof Local){
                            ref_last_used.put(mthd+"_"+expr.getArg(i).toString(),Integer.valueOf(ln));
                        }
                    }
                }
                else{
                    if(expr instanceof JVirtualInvokeExpr){
                        ref_last_used.put(mthd+"_"+((JVirtualInvokeExpr)expr).getBase().toString(),Integer.valueOf(ln));
                    }
                    
                    // if(expr instanceof JStaticInvokeExpr)     System.out.println(expr.getMethod().getSignature());
                    int argCount = expr.getArgCount();
                    // Integer flag = 0;
                    for(int i=0;i<argCount;i++){
                        params_to_child.put(i, mthd+"_"+expr.getArg(i).toString());
                        ref_last_used.put(mthd+"_"+expr.getArg(i).toString(),Integer.valueOf(ln));
                        // System.out.println("string  "+mthd+"_"+expr.getArg(i).toString()+"   last used  "+Integer.valueOf(ln));
                        // flag = 1;
                    }
                    // System.out.println("stmt is -------> "+ u);
                    call_line_number = u.getJavaSourceStartLineNumber();
                }

            }

            // if(u instanceof JStaticInvokeExpr)        System.out.println("Yes");


            stmt_last_processed = u.getJavaSourceStartLineNumber();
        }

        if(stmt_last_processed == body.getUnits().getLast().getJavaSourceStartLineNumber()){
            callPrint = true;
        }

        if(reqs.child != null) {

            mPTG = mergeChild(ptg, params_to_child, params_to_me, retVar, call_line_number , ref_last_used, reqs.child , callPrint, collObjects);
            // Do something and get final PTG store it in mPTG;
        }
        else{
            // print all the objects that can be collected first
            if(reqs.preceedingPTG == null && reqs.begin != -7) { mPTG = ptg; }
            else mPTG = printAndReturn(ptg, params_to_me, ref_last_used, collObjects);

              
        }

        
        // System.out.println("\n\n");
        // mPTG.printGraph();
        // System.out.println("\n\n");
        // System.out.println(ref_last_used);
        // System.out.println("\n\n");
        // System.out.println(params_to_me);
        // System.out.println("\n\n");
        // System.out.println(params_to_child);
        // System.out.println("\n\n");

        // make a copy of ptg and return
        // System.out.println("method:  "+mthd);
        // mPTG.printGraph();
        ptg_params.put(mPTG, params_to_me);
        processCFGReq return_params = new processCFGReq(mPTG,ptg_params,ref_last_used,params_to_me,reqs.method,-7,-7);
        return_params.gcedObjects = collObjects;
        return return_params;
    }

    protected static PTG_Node findObj(PTG ptg, String mthd, Value ref){
        PTG_Node n = null;
        // System.out.println("string is :"+ ref.toString());
        List<PTG_Node> l1 = ptg.findObject(mthd+"_"+ref.toString());
        // System.out.println(mthd+"_"+ref.toString());
        if(l1 != null){
            // System.out.println("list: "+ l1);
            if(l1.isEmpty()){    
                // System.out.println("Ref pointing list is Empty!");
            }
            else{
                return l1.get(0);
            }
        }
        else{
            // System.out.println("Ref is not pointing to any Object");
        }
        return n;
    }

    protected static PTG mergeChild(PTG ptg, Map<Integer,String> params_to_child, Map<Integer,String> params_to_me, String retVar, Integer call_line_number, Map<String,Integer> ref_last_used, Map<PTG,Map<Integer,String>> child, Boolean callPrint, TreeSet<String> collObjects){
        
        PTG childPTG = null;
        Map<Integer,String> childParam = null;
        int n;
        for(Map.Entry<PTG,Map<Integer,String>> m: child.entrySet()){
            childPTG = m.getKey();
            childParam = m.getValue();
        }
        // System.out.println("Child graph");
        // childPTG.printGraph();
        n = params_to_child.size();
        // System.out.println("params -------> " +n);

        PTG_Node dummy, corr;
        for(int i=0;i<n;i++){
            dummy = childPTG.findNode(childPTG.nodes,childParam.get(i));
            corr = ptg.findNode(ptg.nodes,params_to_child.get(i));
            for(Map.Entry<PTG_Node,List<PTG_Node>> k: childPTG.edges.entrySet()){
                if(k.getKey().name.equals(dummy.name)) { dummy = k.getValue().get(0); break;}
            }
            for(Map.Entry<PTG_Node,List<PTG_Node>> k: ptg.edges.entrySet()){
                if(k.getKey().name.equals(corr.name)) { corr = k.getValue().get(0); break; }
            }

            recurMergeParams(ptg, dummy, corr);
            
        }

        // for storing values of invoke stmts
        if(retVar != null) {
            PTG_Node ret = null;
            for(Map.Entry<PTG_Node,List<PTG_Node>> k: childPTG.edges.entrySet()){
                if(k.getKey().name.contains("_return")) ret=k.getValue().get(0); 
            }
            if(!ret.name.contains("Dummy")) ptg.addEdge(new PTG_Node(retVar), null, ret);
        }

        String[] parts = null;
        //free everything left in childPTG
        if(retVar == null && n == 0){
            for(PTG_Node k: childPTG.nodes){
                if(k.name.contains("Object")){
                    parts = k.name.split("_"); 

                    // System.out.println("parts    "+parts + "       objet " + k.name);
                    // if(collObjects == null) System.out.println("coll Objects is null");
                    collObjects.add(parts[1]+":"+call_line_number.toString());
                    // System.out.println("Object:"+k.name+"      collected at line: "+call_line_number);
                    // childPTG.removeNode(k.name); // not needed to call
                }
            }
        }

        if(callPrint) return printAndReturn(ptg, params_to_me, ref_last_used, collObjects);

        return ptg;
       
    }

    protected static void recurMergeParams(PTG ptg, PTG_Node dummy, PTG_Node corr){
        if(!dummy.fields.isEmpty()){
            PTG_Node nextCorr = null;
            for(Map.Entry<String,PTG_Node> f: dummy.fields.entrySet()){
                String field = f.getKey();
                PTG_Node t = f.getValue();
                nextCorr = ptg.findField(corr, field);
                recurMergeParams(ptg, t, nextCorr);
                if(!t.name.contains("Dummy")) ptg.addEdge(corr, field, t); 
            }
        }
    }

    protected static PTG printAndReturn(PTG ptg, Map<Integer,String> params_to_me ,Map<String,Integer> ref_last_used, TreeSet<String> collObjects){

        // Printing the objects that can be collected
        String ref;
        // Scavenging the objects that cannot be collected
        List<String> scavenged = new ArrayList<>();
        for(Map.Entry<String,Integer> l: ref_last_used.entrySet()){
            ref = l.getKey();
            if(ref.contains("_return")) {

                for(Map.Entry<PTG_Node,List<PTG_Node>> c: ptg.edges.entrySet()){
                    if(c.getKey().name.contains("_return")){
                        String str = c.getValue().get(0).name;
                        scavenged.add(str);
                        findReachable(scavenged,ptg,str);
                    }
                }
            }
        }

        String tr;
        for(Map.Entry<Integer,String> m: params_to_me.entrySet()){
            ref = m.getValue();
            for(Map.Entry<PTG_Node,List<PTG_Node>> k: ptg.edges.entrySet()){
                if(k.getKey().name.equals(ref)){
                    tr = k.getValue().get(0).name;
                    scavenged.add(tr);
                    findReachable(scavenged, ptg, tr);
                } 
            }           
        }

        // preparing map of objects that can be collected
        PTG_Node nd;
        String str;
        Integer last_u;
        Map<String,List<String>> gced = new HashMap<>();
        for(Map.Entry<String,Integer> l: ref_last_used.entrySet()){
            ref = l.getKey();
            last_u = l.getValue();
            for(Map.Entry<PTG_Node,List<PTG_Node>> m: ptg.edges.entrySet()){
                if(m.getKey().name.equals(ref)){
                    recurAttach( m.getValue().get(0),ref,last_u,scavenged,gced);
                }
            }
        }

        // printing the gced object
        List<String> val;
        String[] parts;
        String[] pt = null;
        Integer max = -2,temp;
        for(Map.Entry<String,List<String>> m : gced.entrySet()){
            str = m.getKey();
            val = m.getValue();
            // System.out.println("str:   " + str);
            max = -2;
            for(String s: val){
                // System.out.println("val:   " + val);
                parts = s.split("@");
                temp = Integer.valueOf(parts[1]);
                if(max<temp) max = temp;
            }
            // ptg.printGraph();
            pt = str.split("_");
            collObjects.add(pt[1]+":"+max.toString());
            // System.out.println("Object:"+str+"      collected at line: "+max);
            ptg.removeNode(str);
            // ptg.printGraph();
        }
        // System.out.println("printAndReturn called");
        return ptg;
    }

    protected static void recurAttach(PTG_Node n,String ref, Integer last_u, List<String> scavenged , Map<String,List<String>> gced){
        String str = n.name;
        if(!scavenged.contains(str)){
            gced.computeIfAbsent(str, k -> new ArrayList<>()).add(ref+"@"+last_u.toString());
            for(Map.Entry<String,PTG_Node> m: n.fields.entrySet()){
                recurAttach(m.getValue(), ref, last_u, scavenged, gced);
            }
        }
    }

    protected static void findReachable(List<String> scavenged, PTG ptg, String str){
        List<PTG_Node> children = new ArrayList<>(); 
        // System.out.println(str);
        for(Map.Entry<PTG_Node,List<PTG_Node>> c: ptg.edges.entrySet()){
            if(c.getKey().name.equals(str)){
                children = c.getValue();
                if(!children.isEmpty()){
                    for(PTG_Node node: children){
                        scavenged.add(node.name);
                        findReachable(scavenged, ptg, node.name);
                    }
                }
                else return;
                // scavenged.add(str);
                // findReachable(scavenged,ptg,str);
            }
        }
    }
 
    
    protected static void processInOrder(SootMethod method){
        stk.push(method);
        // Queue<Map<PTG,Map<Integer,String>>> queue = new LinkedList<>();
        Map<String,Map<PTG,Map<Integer,String>>> q = new HashMap<>();
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);
        int f = 0;
        SootMethod smt=null;
        // System.out.println(edges.);
        while(edges.hasNext()){
            SootMethod mt = edges.next().tgt();
            if(!mt.isJavaLibraryMethod() && !mt.isConstructor()){  
                if(f != 0) { q.put(smt.getDeclaringClass().toString()+"->"+smt.getName(), args.child); args.child = null; }// enqueue ptg and provide new null ptg 
                // System.out.println("method----------->"+mt.toString());
                processInOrder(mt);
                smt = mt; 
                f++;
            }
        }

        SootMethod m = stk.pop();
        if(!q.isEmpty()){
            // queue.offer(args.child);
            q.put(smt.getDeclaringClass().toString()+"->"+smt.getName(),args.child);
            // System.out.println("*******************  "+smt.toString());
            args = mergeQueue(m,q); // if queue is not empty then process each ptg in queue and store it in pointsTo
            globalGced.put(m.getDeclaringClass().toString()+":"+m.getName(),args.gcedObjects);
            args = new processCFGReq(null, args.child, null, null, null, -7, -7);
            // q.clear(); // not needed

        }else{
            // System.out.println(m.getName());
            // System.out.println("method ----> "+ m);
            args.method = m;
            args.gcedObjects = null;
            args = processCFG(args);
            
            args.preceedingPTG = null;
            args.ref_last_used = null;
            args.params_to_me = null;
            args.method = null;
            args.begin = -7;
            args.end = -7;
            globalGced.put(m.getDeclaringClass().toString()+":"+m.getName(),args.gcedObjects);
        }
    }

    // to be tested
    protected static processCFGReq mergeQueue(SootMethod m, Map<String,Map<PTG,Map<Integer,String>>> q){
        
        // Map<PTG,Map<Integer,String>> preceedingPTG = null;
        processCFGReq arguments = new processCFGReq(null, null, null, null, null, null, null);
        // PTG pPTG = null;
        Integer count = 1,begin=-1,end=0;
        Integer si = q.size();
        while(!q.isEmpty())
        {
            if(count == 1){ begin = -1; arguments.method=m; arguments = getInitialPTG(arguments); }
            else begin = end+1;

            Body b = m.getActiveBody();
            PatchingChain<Unit> units = b.getUnits();
            Integer c=0;
            SootMethod st = null;
            String[] parts;
            Value v1 = null;
            PTG_Node n1 = null;
            String type = null;
            for(Unit u: units){
                if(u instanceof JInvokeStmt){
                    JInvokeStmt invokeStmt = (JInvokeStmt) u;
                    InvokeExpr expr = invokeStmt.getInvokeExpr();
                    if(expr instanceof JVirtualInvokeExpr && ((JVirtualInvokeExpr)expr).getMethod().getSignature().contains("<java.io.PrintStream:"));
                    else if(expr instanceof JVirtualInvokeExpr || expr instanceof JStaticInvokeExpr){
                        c++;
                        if(expr instanceof JVirtualInvokeExpr) {
                            v1 = ((JVirtualInvokeExpr)expr).getBase();
                            n1 = findObj(arguments.preceedingPTG, m.getName().toString(), v1);
                            
                            // System.out.println(v1.toString()+"   n1"+n1);
                            // System.out.println(arguments.preceedingPTG.edges);
                            parts = n1.name.split("#");
                            type = parts[0];
                        }
                        if(expr instanceof JStaticInvokeExpr) {
                            type = ((JStaticInvokeExpr)expr).getMethod().getDeclaringClass().toString();
                            // n1 = findObj(arguments.preceedingPTG, m.toString(), v1);
                            // parts = n1.name.split("#");
                            // type = parts[0];
                        }

                        st = expr.getMethod();
                        // System.out.println("here >>>>>>>>>>>>>>>>>>>>>>>  " +st);
                        if(c==count) { end = u.getJavaSourceStartLineNumber(); break; }
                    }
                }
            }
            
            if(count == si) end = units.getLast().getJavaSourceStartLineNumber();
            // System.out.println("count    "+count+"     size       "+si);
            if(count == 1){

                arguments.preceedingPTG = null;
                arguments.child = q.get(type+"->"+st.getName());
                q.remove(type+"->"+st.getName());
                // System.out.println("size after removing "+q.size());
                arguments.params_to_me = null;
                arguments.ref_last_used = null;
                arguments.method = m;
                arguments.begin = begin;
                arguments.end = end;
                arguments.gcedObjects = null;
                arguments = processCFG(arguments);
            }
            else {
                
                arguments.child = q.get(type+"->"+st.getName());
                q.remove(type+"->"+st.getName());
                // System.out.println("size after removing "+q.size());
                arguments.begin = begin;
                arguments.end = end;
                arguments.method = m;
                arguments = processCFG(arguments); 
            }
            count++;
            // if(count == 4) break;
        }

        return arguments;
    }


    protected static processCFGReq getInitialPTG(processCFGReq args){

        SootMethod m = args.method;
        Body b = m.getActiveBody();
        PatchingChain<Unit> units = b.getUnits();
        for(Unit u: units){
            if(u instanceof JInvokeStmt){
                JInvokeStmt invokeStmt = (JInvokeStmt) u;
                InvokeExpr expr = invokeStmt.getInvokeExpr();
                if(expr instanceof JVirtualInvokeExpr && ((JVirtualInvokeExpr)expr).getMethod().getSignature().contains("<java.io.PrintStream:"));
                else if(expr instanceof JVirtualInvokeExpr || expr instanceof JStaticInvokeExpr){
                    args.end = u.getJavaSourceStartLineNumber(); break;
                }
            }
        }

        args.begin = -1;
        args.gcedObjects = null;
        return processCFG(args);
    }

    protected void printGcedObjects(){
        // System.out.println("\n\n\n");
        String mt;
        TreeSet<String> objs;
        for(Map.Entry<String,TreeSet<String>> m: globalGced.entrySet()){
            mt = m.getKey();
            objs = m.getValue();
            System.out.print(mt+" ");
            for(String s: objs){
                System.out.print(s+" ");
            }
            System.out.println();
        }
    }

}
