-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_classical_conditioning_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.classical_conditioning_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:27:34.297677+00:00
-- url     : https://prove2.me/theorems/c19a999b-9da3-4757-aca6-93d8e54751e4
-- title:
--   6.18
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For both smooth min and max, H^ε(A|YB)≥H^ε(A|B)−log dim Y when Y is classical.
--
--   $$
--   H^\varepsilon(A|YB)_\rho\ge H^\varepsilon(A|B)_\rho-\log_2 d_Y\quad(H=H_{\min},H_{\max}).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 103, 6.18

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

/-- NODE paper:1504.00233#6.18
6.18, arXiv:1504.00233v5, PDF p.103. -/
theorem classical_conditioning_bound [Nonempty A] [Nonempty Y] [Nonempty B] (r : paperMat ((A × Y) × B))
    (hr : paperSubnormalized r) (hc : ∀ a y b a' y' b', y ≠ y' → r ((a,y),b) ((a',y'),b') = 0)
    (e : ℝ) (he : Radius r e) :
    paperSmoothMin (paperTraceMiddle r) e-(Real.logb 2 (Fintype.card Y):EReal) ≤ paperSmoothMin (paperRegroup r) e ∧
    paperSmoothMax (paperTraceMiddle r) e-(Real.logb 2 (Fintype.card Y):EReal) ≤ paperSmoothMax (paperRegroup r) e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
