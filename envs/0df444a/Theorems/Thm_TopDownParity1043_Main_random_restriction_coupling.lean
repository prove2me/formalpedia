-- Prove2me | Theorems.Thm_TopDownParity1043_Main_random_restriction_coupling
-- name    : TopDownParity1043.Main.random_restriction_coupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:02:56.332448+00:00
-- url     : https://prove2.me/theorems/87420566-9bac-422e-afb1-650e4a6da96c
-- title:
--   Random restrictions — union and difference coupling
-- statement:
--   Let $P,Q$ be independent Bernoulli subsets of a finite coordinate set $V$, with respective biases $p,q$. Put $s=p+q-pq$, and choose $r\in[0,1]$ such that $sr=p(1-q)$. If $S,T$ are independent Bernoulli subsets of biases $s,r$, respectively, then every real function $F$ of two subsets satisfies
--
--   $$
--   \mathbb E_{P,Q}F(P\cup Q,P\setminus Q)=\mathbb E_{S,T}F(S,S\cap T).
--   $$
--
--   This is the joint-law form of the random-restriction conditioning identity used in the mirror-set proof. When $s>0$, it says that conditional on $P\cup Q=S$, the set $P\setminus Q$ includes the coordinates of $S$ independently with bias $p(1-q)/s$. The division-free hypotheses also cover endpoint biases. This identity allows fibre estimates on a smaller cube to be averaged over the original restrictions.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission #1043, p.9 conditional law of P\Q given P∪Q=S, reused in the Strong Mirror Set Lemma on p.12 and Section 4 p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
set_option autoImplicit false

theorem TopDownParity1043.Main.random_restriction_coupling (V : Type) [Fintype V] [DecidableEq V]
    (p q s r : TopDownParity1043.Main.Bias)
    (hs : (s : ℝ) = (p : ℝ) + (q : ℝ) - (p : ℝ)*(q : ℝ))
    (hr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (F : Finset V → Finset V → ℝ) :
    (∑ P : Finset V, TopDownParity1043.Main.setWeight p P *
      ∑ Q : Finset V, TopDownParity1043.Main.setWeight q Q * F (P ∪ Q) (P \ Q)) =
    (∑ S : Finset V, TopDownParity1043.Main.setWeight s S *
      ∑ T : Finset V, TopDownParity1043.Main.setWeight r T * F S (S ∩ T)) := by sorry
