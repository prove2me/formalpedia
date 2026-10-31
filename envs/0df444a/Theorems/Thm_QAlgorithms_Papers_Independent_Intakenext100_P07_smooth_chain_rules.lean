-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_chain_rules
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_chain_rules
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:26:12.836601+00:00
-- url     : https://prove2.me/theorems/74fd53b4-a01f-4a52-b752-8dfc16def813
-- title:
--   6.16
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$. Write $g(t)=-\log_2(1-\sqrt{1-t^2})$ for $0<t<1$.
--
--   The six inequalities below hold. δ=ε−εprime−2εdoubleprime>0 and g(δ)=−log(1−sqrt(1−δ²)); coefficients are 1,2,3 and smoothing indices in the displays are binding.
--
--   $$
--   \begin{aligned}H_{\min}^{\varepsilon}(AB|C)&\ge H_{\min}^{\varepsilon^\prime}(A|BC)+H_{\min}^{\varepsilon^{\prime\prime}}(B|C)-g(\delta),\\H_{\min}^{\varepsilon^\prime}(AB|C)&\le H_{\min}^{\varepsilon}(A|BC)+H_{\max}^{\varepsilon^{\prime\prime}}(B|C)+2g(\delta),\\H_{\min}^{\varepsilon^\prime}(AB|C)&\le H_{\max}^{\varepsilon^{\prime\prime}}(A|BC)+H_{\min}^{\varepsilon}(B|C)+3g(\delta),\\H_{\max}^{\varepsilon}(AB|C)&\le H_{\max}^{\varepsilon^\prime}(A|BC)+H_{\max}^{\varepsilon^{\prime\prime}}(B|C)+g(\delta),\\H_{\max}^{\varepsilon^\prime}(AB|C)&\ge H_{\min}^{\varepsilon^{\prime\prime}}(A|BC)+H_{\max}^{\varepsilon}(B|C)-2g(\delta),\\H_{\max}^{\varepsilon^\prime}(AB|C)&\ge H_{\max}^{\varepsilon}(A|BC)+H_{\min}^{\varepsilon^{\prime\prime}}(B|C)-3g(\delta).\end{aligned}
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 103, 6.16

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

/-- NODE paper:1504.00233#6.16
6.16, arXiv:1504.00233v5, PDF p.103. -/
theorem smooth_chain_rules [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : paperSubnormalized r) (e ep epp : ℝ) (he : Radius r e) (hep : Radius r ep) (hepp : Radius r epp)
    (hg : ep+2*epp < e) :
    paperSmoothMin (paperRegroup r) ep+paperSmoothMin (paperMarginalBC r) epp-(paperPenalty (e-ep-2*epp):EReal) ≤ paperSmoothMin r e ∧
    paperSmoothMin r ep ≤ paperSmoothMin (paperRegroup r) e+paperSmoothMax (paperMarginalBC r) epp+((2*paperPenalty (e-ep-2*epp):ℝ):EReal) ∧
    paperSmoothMin r ep ≤ paperSmoothMax (paperRegroup r) epp+paperSmoothMin (paperMarginalBC r) e+((3*paperPenalty (e-ep-2*epp):ℝ):EReal) ∧
    paperSmoothMax r e ≤ paperSmoothMax (paperRegroup r) ep+paperSmoothMax (paperMarginalBC r) epp+(paperPenalty (e-ep-2*epp):EReal) ∧
    paperSmoothMin (paperRegroup r) epp+paperSmoothMax (paperMarginalBC r) e-((2*paperPenalty (e-ep-2*epp):ℝ):EReal) ≤ paperSmoothMax r ep ∧
    paperSmoothMax (paperRegroup r) e+paperSmoothMin (paperMarginalBC r) epp-((3*paperPenalty (e-ep-2*epp):ℝ):EReal) ≤ paperSmoothMax r ep := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
