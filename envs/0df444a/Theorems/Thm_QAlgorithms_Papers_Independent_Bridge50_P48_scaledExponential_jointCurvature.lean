-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P48_scaledExponential_jointCurvature
-- name    : QAlgorithms.Papers.Independent.Bridge50.P48.scaledExponential_jointCurvature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:58:20.110677+00:00
-- url     : https://prove2.me/theorems/67b5331c-8376-48ab-b20d-1e8bc544d788
-- title:
--   Joint curvature of the scaled entropy exponential
-- statement:
--   Fix a complex Hilbert space and a finite real number $t>0$. On pairs of nonnegative trace-class operators $(\rho,\sigma)$ with $\operatorname{Tr}\rho=t$, set $F_\alpha(\rho,\sigma)=Q_\alpha(\rho,\sigma)/t$, where $Q_\alpha$ is the extended sandwiched spectral trace. This is the extended interpretation of $\exp((\alpha-1)D_\alpha(\rho\Vert\sigma))$. For two such pairs and their common-weight convex combination $(\rho_\lambda,\sigma_\lambda)$, $\lambda\in[0,1]$,
--
--   $$\begin{aligned}F_\alpha(\rho_\lambda,\sigma_\lambda)&\ge\lambda F_\alpha(\rho_1,\sigma_1)+(1-\lambda)F_\alpha(\rho_2,\sigma_2)&& (1/2\le\alpha<1),\\ F_\alpha(\rho_\lambda,\sigma_\lambda)&\le\lambda F_\alpha(\rho_1,\sigma_1)+(1-\lambda)F_\alpha(\rho_2,\sigma_2)&& (\alpha>1).\end{aligned}$$
--
--   Both ranges consist of finite real orders. Orthogonal supports give $F_\alpha=0$ below one and infinity above one. The trace need not equal one.
--
--   This records the normalized consequence separately from the unnormalized trace inequality.
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, PDF p. 2, Consequence after Proposition 3: exp((alpha-1)D_alpha)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Frank--Lieb, PDF p.2, unnumbered consequence after Proposition 3:
joint curvature of exp((alpha-1)D_alpha) on every fixed positive trace slice. -/
theorem scaledExponential_jointCurvature {I : Type*} (b : HilbertBasis I ℂ H)
    (t : ℝ) (ht : 0 < t) (alpha : ℝ) :
    ((1 / 2 : ℝ) ≤ alpha → alpha < 1 →
      jointConcaveOn (traceSlice b t) (scaledExponential b t alpha)) ∧
    (1 < alpha → jointConvexOn (traceSlice b t) (scaledExponential b t alpha)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P48

end
