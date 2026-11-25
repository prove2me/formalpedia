-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_exp_neg_mul_norm_sq_euclidean
-- name    : ReciprocityTheory.ChartRestriction.G.I2.integrable_exp_neg_mul_norm_sq_euclidean
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:48.642182+00:00
-- url     : https://prove2.me/theorems/6ac50483-dc17-5e5f-98a2-17192b8874f4
-- title:
--   I2: integrable exp neg mul norm sq euclidean
-- statement:
--   The I2 construction uses the integrable exp neg mul norm sq euclidean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegrableNormPowMulExpNegMulNormSq.lean#L69-L77

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

theorem ReciprocityTheory.ChartRestriction.G.I2.integrable_exp_neg_mul_norm_sq_euclidean {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by sorry
