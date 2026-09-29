-- Prove2me | Theorems.Thm_RobustMeanCov_Projection_standardize_mem
-- name    : RobustMeanCov.Projection.standardize_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:44:34.656703+00:00
-- url     : https://prove2.me/theorems/21d8210e-5442-4ffa-a2fa-abb9e528dec6
-- title:
--   Standardizing a $(m,v)$ law with $v>0$ gives a $(0,1)$ law
-- statement:
--   Let $m\in\mathbb{R}$ and $v>0$. If a random variable $\mathbf r$ has a law in $\mathbb{M}_{(m,v)}$, then
--
--   $$
--   \mathbf z = v^{-1/2}(\mathbf r - m)
--   $$
--
--   has a law in $\mathbb{M}_{(0,1)}$, that is, $E[\mathbf z]=0$ and $\operatorname{Var}[\mathbf z]=1$.
--
--   In the proof of the general projection property this is applied with $m = x'\mu$ and $v = x'\Sigma x$, reducing the target law to a standardized one.
--
--   **Formalization Note** The hypothesis $v>0$ is the case the proof is in after its first sentence; it also keeps the real power $v^{-1/2}$ away from its default value at non-positive arguments.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, https://doi.org/10.1287/opre.1060.0353, p. 109, Appendix, proof of Theorem 1, (1) and the sentence after it

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

/-- Appendix, proof of Theorem 1, (1) (Popescu 2007, p. 109): standardizing a law with mean `m`
and variance `v > 0` by `z = v^{-1/2}(r - m)` gives a law with mean 0 and variance 1. -/
theorem standardize_mem (m v : ℝ) (hv : 0 < v) (ν : Measure ℝ) (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m v) :
    ν.map (fun r => v ^ (-(1 / 2 : ℝ)) * (r - m)) ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := by sorry

end RobustMeanCov.Projection
