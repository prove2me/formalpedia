-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomialKernel_mul_gaussian_half
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian_half
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:42.240688+00:00
-- url     : https://prove2.me/theorems/1a32604d-f50a-48ad-9257-0626c429db2e
-- title:
--   I2: integral monomial Kernel mul gaussian half
-- statement:
--   The I2 construction uses the integral monomial Kernel mul gaussian half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L100-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L100-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian_half {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) := by sorry
