-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_schatten_variational
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.schatten_variational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:59:37.693184+00:00
-- url     : https://prove2.me/theorems/c7b7f6df-7319-4247-9e53-a5f76f39a573
-- title:
--   3.4
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For M≥0,p>0,r=1−1/p, ||M||_p=max_{N≥0,Tr N=1}Tr(M N^r) for p≥1 and min_{N≥0,Tr N=1,M≪N}Tr(M N^r) for 0<p≤1. Both extrema attained.
--
--   $$
--   \|M\|_p=\max_{N\in\mathcal S_\circ}\operatorname{Tr}(MN^{1-1/p})\ (p\ge1),\qquad\|M\|_p=\min_{N\in\mathcal S_\circ,\ M\ll N}\operatorname{Tr}(MN^{1-1/p})\ (p\le1).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 41, 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#3.4
3.4, arXiv:1504.00233v5, PDF p.41. -/
theorem schatten_variational [Nonempty I] (M : paperMat I) (hM : M.PosSemidef) (p : ℝ) (hp : 0 < p) :
    (1 ≤ p → (∃ N : paperMat I, IsDensityMatrix N ∧ (M*paperPower N (1-1/p)).trace.re = paperSchatten M p) ∧
      ∀ N : paperMat I, IsDensityMatrix N → (M*paperPower N (1-1/p)).trace.re ≤ paperSchatten M p) ∧
    (p ≤ 1 → (∃ N : paperMat I, IsDensityMatrix N ∧ paperSupported M N ∧ (M*paperPower N (1-1/p)).trace.re = paperSchatten M p) ∧
      ∀ N : paperMat I, IsDensityMatrix N → paperSupported M N → paperSchatten M p ≤ (M*paperPower N (1-1/p)).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
