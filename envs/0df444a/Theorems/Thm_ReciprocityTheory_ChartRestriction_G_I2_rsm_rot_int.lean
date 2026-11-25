-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_rot_int
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_rot_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:58.805407+00:00
-- url     : https://prove2.me/theorems/ec94f2c7-e04c-5522-90dc-833132b0daf4
-- title:
--   I2: rsm rot int
-- statement:
--   The I2 construction uses the rsm rot int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L220-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L220-L242

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_rot_int (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F (u • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by sorry
