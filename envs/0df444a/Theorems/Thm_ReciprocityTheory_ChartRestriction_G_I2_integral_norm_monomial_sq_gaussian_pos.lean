-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_pos
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_pos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:48.148006+00:00
-- url     : https://prove2.me/theorems/75deff3a-efd3-4e13-a01a-cf2524f2b665
-- title:
--   I2: integral norm monomial sq gaussian pos
-- statement:
--   The I2 construction uses the integral norm monomial sq gaussian pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L173-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L173-L192

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

theorem ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_pos {g : ℕ} (α : Fin g →₀ ℕ) :
    0 < ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
