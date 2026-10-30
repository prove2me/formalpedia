-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P48_divergenceExponential_jointConvexity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P48.divergenceExponential_jointConvexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:59:04.915969+00:00
-- url     : https://prove2.me/theorems/4b9114f8-36bd-48d1-bbe2-0a497384f6ac
-- title:
--   Joint convexity of exp(D_alpha) for orders up to two
-- statement:
--   Fix a complex Hilbert space, a finite real number $t>0$, and an order $1<\alpha\le2$. For a pair of nonnegative trace-class operators with $\operatorname{Tr}\rho=t$, set
--
--   $$G_\alpha(\rho,\sigma)=\left(Q_\alpha(\rho,\sigma)/t\right)^{1/(\alpha-1)}=\exp(D_\alpha(\rho\Vert\sigma)).$$
--
--   For two such pairs, let $(\rho_\lambda,\sigma_\lambda)=\lambda(\rho_1,\sigma_1)+(1-\lambda)(\rho_2,\sigma_2)$, using a common $\lambda\in[0,1]$. Then
--
--   $$G_\alpha(\rho_\lambda,\sigma_\lambda)\le\lambda G_\alpha(\rho_1,\sigma_1)+(1-\lambda)G_\alpha(\rho_2,\sigma_2).$$
--
--   The function takes nonnegative extended values, with infinity on failed support inclusion. The exponent is positive and the logarithm convention is natural.
--
--   This is convexity of the exponential, rather than a claim of convexity of the entropy above one. The paper also attributes this consequence to [12] and [15].
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, PDF p. 2, Consequence after Proposition 3: exp(D_alpha)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Frank--Lieb, PDF p.2, unnumbered consequence after Proposition 3:
exp(D_alpha) is jointly convex for 1<alpha<=2 on a fixed positive trace slice. -/
theorem divergenceExponential_jointConvexity {I : Type*} (b : HilbertBasis I ℂ H)
    (t : ℝ) (ht : 0 < t) (alpha : ℝ) (halpha : 1 < alpha ∧ alpha ≤ 2) :
    jointConvexOn (traceSlice b t) (divergenceExponential b t alpha) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P48

end
