(* La librairie strandard est décrite ici

   https://coq.inria.fr/distrib/current/stdlib/

*)

Require Import List. (* Voir https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html *)

Reserved Notation "x '~p' y" (at level 70, no associativity).

Section list_perm.

  Variable X : Type.

  Inductive perm : list X -> list X -> Prop :=

    | perm_nil   :                    nil ~p nil

    | perm_cons  : forall x l1 l2,     l1 ~p l2 
                               ->   x::l1 ~p x::l2

    | perm_swap  : forall x y l,  x::y::l ~p y::x::l

    | perm_trans : forall l1 l2 l3,    l1 ~p l2 
                               ->      l2 ~p l3 
                               ->      l1 ~p l3

  where "x '~p' y " := (perm x y).

  Fact perm_refl l : l ~p l.
  Proof.
  Admitted.

  Fact perm_length l1 l2 : l1 ~p l2 -> length l1 = length l2.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].    
  Admitted.

  Fact perm_sym l1 l2 : l1 ~p l2 -> l2 ~p l1.
  Proof.
  Admitted.

  Fact perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
    induction l as [ | y l IHl ]; simpl.
  Admitted.

  Let perm_app_left l r1 r2 : r1 ~p r2 -> l++r1 ~p l++r2.
  Proof.
    intros H.
    induction l; simpl.
  Admitted.

  Fact perm_app l1 l2 r1 r2 : l1 ~p l2 -> r1 ~p r2 -> l1++r1 ~p l2++r2.
  Proof.
    intros H; revert H r1 r2.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ].
  Admitted.

  (* incl est défini dans la librairie standard, fichier List.v *)

  Print incl.

  Fact perm_incl l m : l ~p m -> incl l m.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; simpl; auto.
  Admitted.

End list_perm.

Infix "~p" := (perm _) (at level 70, no associativity).
