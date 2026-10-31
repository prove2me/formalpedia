-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_angle_comparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_angle_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:25:33.546322+00:00
-- url     : https://prove2.me/theorems/ae97bf76-1226-4db2-8e74-ec74367f9a4b
-- title:
--   6.15
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For normalized ρ_AB and φ,θ≥0, φ+θ<π/2, Hmin^{sinφ}(A|B)≤Hmax^{sinθ}(A|B)+2log(1/cos(φ+θ)).
--
--   $$
--   H_{\min}^{\sin\varphi}(A|B)_\rho\le H_{\max}^{\sin\vartheta}(A|B)_\rho+2\log_2\frac1{\cos(\varphi+\vartheta)}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 102, 6.15

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

/-- NODE paper:1504.00233#6.15
6.15, arXiv:1504.00233v5, PDF p.102. -/
theorem smooth_angle_comparison [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b < Real.pi/2) :
    paperSmoothMin r (Real.sin a) ≤ paperSmoothMax r (Real.sin b)+((2*Real.logb 2 (1/Real.cos (a+b)) : ℝ):EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
