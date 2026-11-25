-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sq_norm_zero_le_gauss_ball
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sq_norm_zero_le_gauss_ball
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:16.77405+00:00
-- url     : https://prove2.me/theorems/b3925f69-6236-48e9-999e-c7ec7fd58a61
-- title:
--   I2: sq norm zero le gauss ball
-- statement:
--   The I2 construction uses the sq norm zero le gauss ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L259-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L259-L326

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set

theorem ReciprocityTheory.ChartRestriction.G.I2.sq_norm_zero_le_gauss_ball {N : ℕ} (F : EuclideanSpace ℂ (Fin N) → ℂ)
    (hF : Differentiable ℂ F) :
    ‖F 0‖ ^ 2 ≤ 2 / Real.pi ^ N *
      ∫ z in Metric.closedBall 0 (Real.sqrt (2 * N)), ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
