-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_pt_out
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_pt_out
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:28.919213+00:00
-- url     : https://prove2.me/theorems/d73fe027-95e8-45e0-a816-033d3a843ebe
-- title:
--   I: ap pt out
-- statement:
--   The I construction uses the ap pt out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L40-L46

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.ap_pt_out (u E η X : ℝ) (hη : 0 < η) :
    (Real.sqrt 0 + u * Real.sqrt ((X + 1) ^ 2 / ((X + 1) ^ 2 + η))) ^ 2 * (E / η) =
      u ^ 2 * (E / η) - u ^ 2 * (E / ((X + 1) ^ 2 + η)) := by sorry
