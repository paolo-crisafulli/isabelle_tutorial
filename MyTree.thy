theory MyTree
  
  imports Main
    
begin
  
  (* declare [[names_short]] *)
  
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  
  (*
Exercise 2.6. 
Starting from the type 'a tree defined in the text, define a function
contents :: 'a tree \<Rightarrow> 'a list that collects all values in a tree in a list,
in any order, without removing duplicates. 
Then define a function 
treesum :: nat tree \<Rightarrow> nat 
that sums up all values in a tree of natural numbers and prove
treesum t = listsum (contents t)
  *)
  
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil" |
  "contents (Node l x r) = (contents l) @ (x # (contents r))"
  
fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum (Node l x r) = (treesum l) + x + (treesum r)"
  
fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum [] = 0" |
  "listsum (x # xs) = x + (listsum xs)"
  
lemma l0 [simp] : "listsum(xs @ ys) = (listsum xs) + (listsum ys)"
  apply(induction xs)
   apply(auto)
  done
    
theorem treesum_is_listsum_of_contents: "treesum t = listsum (contents t)"
  apply(induction t)
   apply(auto)
  done
