From LF Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
intros n.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
intros n.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros n.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros n m.
induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n m.
induction n as [| n' IHn'].
- rewrite <- plus_n_O_firsttry. simpl. reflexivity.
- rewrite <- plus_n_Sm. rewrite <- IHn'. simpl. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n IHn'].
- simpl. reflexivity.
- simpl. 
rewrite -> plus_n_Sm.
 rewrite <- IHn'. 
 rewrite <- plus_n_Sm.
 reflexivity.
Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n IHn'].
- simpl. reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. 
  induction n as [| n IHn']. 
  - simpl. rewrite -> mult_0_r. reflexivity.
  - induction m as [| m IHm'].
  -- simpl. rewrite -> mult_0_r. reflexivity. 
  -- simpl. rewrite <- IHn'. 