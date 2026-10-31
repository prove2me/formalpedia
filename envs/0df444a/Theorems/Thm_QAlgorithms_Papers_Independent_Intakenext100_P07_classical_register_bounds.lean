-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_register_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_register_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:26:54.326852+00:00
-- url     : https://prove2.me/theorems/617f9ae8-77ab-4c27-b68a-e3b7479be061
-- title:
--   6.17
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For both smooth min and max, H^ε(A|B)≤H^ε(XA|B)≤H^ε(A|B)+log dim X when X is classical.
--
--   $$
--   H^\varepsilon(A|B)_\rho\le H^\varepsilon(XA|B)_\rho\le H^\varepsilon(A|B)_\rho+\log_2 d_X\quad(H=H_{\min},H_{\max}).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 103, 6.17

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

/-- NODE paper:1504.00233#6.17
6.17, arXiv:1504.00233v5, PDF p.103. -/
theorem classical_register_bounds [Nonempty X] [Nonempty A] [Nonempty B] (r : paperMat ((X × A) × B))
    (hr : paperSubnormalized r) (hc : ClassicalLeft (paperRegroup r)) (e : ℝ) (he : Radius r e) :
    paperSmoothMin (traceLeft (paperRegroup r)) e ≤ paperSmoothMin r e ∧
    paperSmoothMin r e ≤ paperSmoothMin (traceLeft (paperRegroup r)) e+(Real.logb 2 (Fintype.card X):EReal) ∧
    paperSmoothMax (traceLeft (paperRegroup r)) e ≤ paperSmoothMax r e ∧
    paperSmoothMax r e ≤ paperSmoothMax (traceLeft (paperRegroup r)) e+(Real.logb 2 (Fintype.card X):EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
