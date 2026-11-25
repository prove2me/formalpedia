-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_half
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_half
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:42.749306+00:00
-- url     : https://prove2.me/theorems/159d6845-1dc4-5a63-aaef-606a0b124c23
-- title:
--   I2: integral norm monomial sq gaussian half
-- statement:
--   The I2 construction uses the integral norm monomial sq gaussian half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L194-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L194-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
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

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_half {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
