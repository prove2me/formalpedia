-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smoothing_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smoothing_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:52:31.972985+00:00
-- url     : https://prove2.me/theorems/ed254a1a-5e25-48ae-85f4-79f7e5f6846c
-- title:
--   §6.2.2: attained extrema, radius monotonicity, zero smoothing
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   Both smooth entropy extrema are attained; Hmin^ε increases and Hmax^ε decreases in radius; at zero radius they equal the respective unsmoothed entropies.
--
--   $$
--   \varepsilon\le\varepsilon^\prime\Longrightarrow H_{\min}^{\varepsilon}\le H_{\min}^{\varepsilon^\prime},\quad H_{\max}^{\varepsilon}\ge H_{\max}^{\varepsilon^\prime},\qquad H_{\min}^0=H_{\min},\quad H_{\max}^0=H_{\max}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 98, §6.2.2: attained extrema, radius monotonicity, zero smoothing

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

/-- NODE paper:1504.00233#6.smoothingproperties
§6.2.2: attained extrema, radius monotonicity, zero smoothing, arXiv:1504.00233v5, PDF p.98. -/
theorem smoothing_properties [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : paperSubnormalized r)
    (e ep : ℝ) (he : Radius r e) (hep : Radius r ep) :
    (∃ t ∈ paperBall r e, paperSmoothMin r e = paperHmin t) ∧ (∃ t ∈ paperBall r e, paperSmoothMax r e = hmax t) ∧
    (e ≤ ep → paperSmoothMin r e ≤ paperSmoothMin r ep ∧ paperSmoothMax r ep ≤ paperSmoothMax r e) ∧
    paperSmoothMin r 0 = paperHmin r ∧ paperSmoothMax r 0 = hmax r := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
