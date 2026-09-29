-- Prove2me | Theorems.Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits
-- name    : ValuationSubring.natDegree_map_eq_card_roots_of_splits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/1fdef6b1-afb0-5113-9744-045f8f270a68
-- title:
--   Degree of the reduction equals the number of integral roots
-- statement:
--   Let $E$ and $k$ be fields, let $A$ be a valuation subring of $E$, and let $\sigma \colon A \to k$ be a ring homomorphism whose kernel is the maximal ideal of the local ring $A$. Let $p \in A[X]$ be a polynomial subject to two hypotheses: first, the reduction $p^{\sigma} \in k[X]$, obtained by applying $\sigma$ to the coefficients of $p$, is nonzero; second, $p$ splits completely over $E$, in the sense that the multiset of roots in $E$ of the image of $p$ under the structure map $A \to E$ has cardinality equal to $\deg p$ (so that all $\deg p$ roots, counted with multiplicity, lie in $E$). The conclusion is that the degree of $p^{\sigma}$ equals the cardinality of the multiset of roots of $p$ in $A$ itself, i.e. the number of roots of $p$ lying in the valuation ring, counted with multiplicity. Equivalently, $\deg p - \deg p^{\sigma}$ counts, with multiplicity, those roots of $p$ in $E$ of negative valuation.
--
--   This is the elementary one-segment Newton-polygon count for a polynomial over a valuation ring: reduction modulo the maximal ideal destroys exactly the roots outside the ring. It is used in the proof of [`AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction`](thm.html#AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction), the comparison, due to Deuring, between the divisor of a rational function and the divisor of its reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Polynomial

theorem ValuationSubring.natDegree_map_eq_card_roots_of_splits
    {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
    (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (p : A[X]) (hp : p.map σ ≠ 0)
    (hsplit : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree) :
    (p.map σ).natDegree = Multiset.card p.roots := by sorry
