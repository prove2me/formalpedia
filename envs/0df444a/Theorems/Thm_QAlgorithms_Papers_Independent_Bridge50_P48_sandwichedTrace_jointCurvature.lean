-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P48_sandwichedTrace_jointCurvature
-- name    : QAlgorithms.Papers.Independent.Bridge50.P48.sandwichedTrace_jointCurvature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:57:47.421086+00:00
-- url     : https://prove2.me/theorems/7825a013-7fee-4ad0-9e0c-1864dfc87bf4
-- title:
--   Joint curvature of the unnormalized sandwiched spectral trace
-- statement:
--   On a complex Hilbert space, define the extended nonnegative spectral trace
--
--   $$Q_\alpha(\rho,\sigma)=\operatorname{Tr}\!\left[\left(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)}\right)^\alpha\right]$$
--
--   for bounded nonnegative operators $\rho,\sigma$. Above one, negative powers have the extended spectral interpretation, including infinity when no finite spectral trace exists. For two such pairs, let $(\rho_\lambda,\sigma_\lambda)=\lambda(\rho_1,\sigma_1)+(1-\lambda)(\rho_2,\sigma_2)$, with the same $\lambda\in[0,1]$ in both components. Then
--
--   $$\begin{aligned}Q_\alpha(\rho_\lambda,\sigma_\lambda)&\ge\lambda Q_\alpha(\rho_1,\sigma_1)+(1-\lambda)Q_\alpha(\rho_2,\sigma_2)&& (1/2\le\alpha<1),\\ Q_\alpha(\rho_\lambda,\sigma_\lambda)&\le\lambda Q_\alpha(\rho_1,\sigma_1)+(1-\lambda)Q_\alpha(\rho_2,\sigma_2)&& (\alpha>1).\end{aligned}$$
--
--   No trace normalization or support inclusion is imposed. All arithmetic here is nonnegative extended arithmetic; the endpoint weights select the corresponding pair exactly.
--
--   This is the spectral trace curvature underlying both entropy theorems.
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, PDF p. 2, Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Frank--Lieb, PDF p.2, Proposition 3; proof on PDF p.4.
The alpha power is applied to the whole sandwich before taking the trace.
The concavity interval includes 1/2; the convexity interval has no upper bound. -/
theorem sandwichedTrace_jointCurvature {I : Type*} (b : HilbertBasis I ℂ H) (alpha : ℝ) :
    ((1 / 2 : ℝ) ≤ alpha → alpha < 1 →
      jointConcaveOn positivePairs (hilbertSandwichedTrace b alpha)) ∧
    (1 < alpha → jointConvexOn positivePairs (hilbertSandwichedTrace b alpha)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P48

end
