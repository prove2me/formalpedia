-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_monomialKernel_mul_gaussian
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integrable_monomialKernel_mul_gaussian
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:38.01819+00:00
-- url     : https://prove2.me/theorems/a8dd20bf-e1f5-5e36-8351-4d8534a2aa21
-- title:
--   I2: integrable monomial Kernel mul gaussian
-- statement:
--   The I2 construction uses the integrable monomial Kernel mul gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean#L66-L72

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

theorem ReciprocityTheory.ChartRestriction.G.I2.integrable_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-b * ‖z‖ ^ 2)) := by sorry
