-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_ball_mass
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_ball_mass
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:46.745343+00:00
-- url     : https://prove2.me/theorems/784f8ca8-4b75-4532-9cbb-5205e9f26b66
-- title:
--   I2: rsm ball mass
-- statement:
--   The I2 construction uses the rsm ball mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L110-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L110-L167

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_ball_mass (N : ℕ) :
    Real.pi ^ N / 2 ≤
      ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)), Real.exp (-‖z‖ ^ 2) := by sorry
