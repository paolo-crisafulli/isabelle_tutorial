theory MyList
  
  imports Main
    
begin
  
declare [[names_short]]
  
datatype 'a list = Nil | Cons 'a "'a list"
  
fun app :: "'a list => 'a list => 'a list" where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"
  
fun rev :: "'a list => 'a list" where
  "rev Nil = Nil" |
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
  
value "rev(Cons True (Cons False Nil))"
  
lemma rev_app [simp]: "rev(app xs (Cons x Nil)) = app (rev(Cons x Nil)) (rev xs)"
  apply(induction xs)
   apply(auto)
  done
    
theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induction xs)
   apply(auto)
  done
    
    (* Ex. 2.1 *)
value "1 + (2::nat)"
  
  
value "1 - (2::nat)"
  
value "1 - (2::int)"
  
  
  (* 
Ex. 2.2
Start from the definition of add given above. Prove that
add is associative and commutative. 
Define a recursive function double :: nat \<Rightarrow> nat 
and prove double m = add m m.
*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add ( Suc m ) n = Suc ( add m n )"
  
lemma add_n_0 [simp]: "add n 0 = n"
  apply(induction n)
   apply(auto)
  done
    
theorem add_is_associative: "add (add m n) l = add m (add n l)"
  apply(induction m)
   apply(auto)
  done
    
    
lemma add_suc_on_the_right[simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done
    
theorem add_is_commutative: "add m n = add n m"
  apply(induction m)
   apply(auto)
  done
    
    (* (Ex. 2.3, part 2)
Define a recursive function double :: nat \<Rightarrow> nat 
and prove double m = add m m.
*)
fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"
  
theorem double_m_is_add_m_to_m: "double m = add m m"
  apply(induction m)
   apply(auto)
  done
    
    (* 
Ex. 2.3
 Define a function count :: 'a \<Rightarrow> 'a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. 
Prove count x xs \<le> length xs.
*)
fun length :: "'a list \<Rightarrow> nat" where
  "length Nil = 0" |
  "length (Cons x xs) = length xs +1"
  
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count y Nil = 0" |
  "count y (Cons x xs) = 
   (if y=x then ((count y xs)+1) else (count y xs))" 
  
theorem count_is_less_than_list_size: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done
    
    (*
Exercise 2.4. Define a recursive function snoc :: 'a list \<Rightarrow> 'a \<Rightarrow> 'a list
that appends an element to the end of a list. With the help of snoc define
a recursive function reverse :: 'a list \<Rightarrow> 'a list that reverses a list. 
Prove reverse (reverse xs) = xs.
*)
    
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = Cons x Nil" |
  "snoc (Cons x xs) y = Cons x (snoc xs y)"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = snoc (reverse xs) x"
  
lemma l0 [simp] : "reverse (snoc xs x) = Cons x (reverse xs)"
  apply(induction xs)
   apply(auto)
  done
    
theorem reverse_is_involutive: "reverse(reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done
    
    (*
Exercise 2.5.
Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
sum_upto n = 0 + ... + n and prove sum_upto n = n \<^emph> (n + 1) div 2.
*)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (sum_upto n) + (Suc n)"

theorem sum_upto_formula [simp] : "sum_upto n = (n * (n + 1)) div 2"
  apply(induction n)
    apply(auto)
done
  
end