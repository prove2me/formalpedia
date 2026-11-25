-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomialKernel_mul_gaussian
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:30.582248+00:00
-- url     : https://prove2.me/theorems/b3cbf92a-b8b9-5b2e-9452-0543d672c97a
-- title:
--   I2: integral monomial Kernel mul gaussian
-- statement:
--   The I2 construction uses the integral monomial Kernel mul gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L74-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L74-L98

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

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) = Real.pi ^ g * p.support.card := by sorry
