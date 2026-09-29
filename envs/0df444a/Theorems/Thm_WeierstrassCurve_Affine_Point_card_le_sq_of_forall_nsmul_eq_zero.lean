-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero
-- name    : WeierstrassCurve.Affine.Point.card_le_sq_of_forall_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/9604ddee-369d-5f69-a0b1-ef1f8b65d45e
-- title:
--   At most n² points killed by n when n is invertible
-- statement:
--   Let $F$ be a field with decidable equality and let $W$ be a Weierstrass curve over $F$ which is elliptic, i.e. carries the `IsElliptic` hypothesis (invertible discriminant). Let $n$ be a natural number whose image in $F$ is non-zero — this in particular forces $n \neq 0$ — and let $S$ be a finite set of points of the associated affine curve, that is, a finite subset of the group `W.toAffine.Point` consisting of the point at infinity together with the nonsingular affine solutions of the Weierstrass equation, with its usual chord-and-tangent group law. Assume that every $P \in S$ is killed by $n$, i.e. $n \bullet P = 0$ in that group. Then the cardinality of $S$ is at most $n^2$. The statement is phrased for an arbitrary finite set of $n$-torsion points rather than for the $n$-torsion subgroup itself, so no finiteness of $W(F)[n]$ is assumed; applied to all finite subsets it says exactly that $W(F)[n]$ has at most $n^2$ elements.
--
--   This is the standard bound on the $n$-torsion of an elliptic curve over a field in which $n$ is invertible, here in the cardinality form convenient for counting arguments. It is used in the construction of Drinfeld bases, via [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj), and rests on the characterisation of odd torsion by the vanishing of division polynomials recorded in [`WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi`](thm.html#WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_card_le_sq_of_forall_nsmul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.Affine.Point.card_le_sq_of_forall_nsmul_eq_zero
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (hn : (n : F) ≠ 0) (S : Finset W.toAffine.Point) (hS : ∀ P ∈ S, n • P = 0) :
    S.card ≤ n ^ 2 := by sorry
