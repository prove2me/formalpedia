-- Prove2me | Theorems.Thm_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero
-- name    : WeierstrassCurve.sum_eq_zero_of_forall_mem_iff_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c1433814-ee33-55c0-8518-c7e80d81fa07
-- title:
--   The n-torsion points of an elliptic curve sum to O
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $n$ be a natural number whose image in $K$ is nonzero, and let $s$ be a finite set of points of the affine elliptic curve obtained from $W$ by base change to $K$, i.e. of the group $(W_{/K})(K)$ in Mathlib's `Point` presentation (the nonsingular affine points together with the point at infinity, with the chord–tangent group law). Assume that $s$ consists exactly of the $n$-torsion: for every point $P$, one has $P \in s$ if and only if $n \cdot P = 0$. Then the sum of all elements of $s$, taken in the group $(W_{/K})(K)$, is the identity $0$. Since $n$ is nonzero in $K$, the hypothesis in particular forces $n \geq 1$, so $s$ is the full group $(W_{/K})(K)[n]$ of $n$-division points.
--
--   This is the classical assertion that the sum of all $n$-division points of an elliptic curve over an algebraically closed field of residue characteristic not dividing $n$ is the origin; it underlies the verification that the divisor $\sum_{R \in E[n]} (T'+R) - \sum_{R \in E[n]} (R)$ is principal in Silverman's construction of the Weil pairing. Within the present development it is used in the computation of the valuation of the Weil numerator, [`WeierstrassCurve.Affine.valuation_weilNum`](thm.html#WeierstrassCurve.Affine.valuation_weilNum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.sum_eq_zero_of_forall_mem_iff_smul_eq_zero {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hnK : (n : K) ≠ 0) (s : Finset (W⁄K).Point) (hs : ∀ P, P ∈ s ↔ n • P = 0) : ∑ P ∈ s, P = 0 := by sorry
