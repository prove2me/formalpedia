-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_pt_in
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_pt_in
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:12.5768+00:00
-- url     : https://prove2.me/theorems/6664c516-7252-4121-9cb7-20e075875853
-- title:
--   I: ap pt in
-- statement:
--   The I construction uses the ap pt in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyC.lean#L17-L38

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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_pt_in (u E η D a I : ℝ) (hu : 0 ≤ u) (hE : 0 ≤ E) (h8 : 8 ≤ η) (hD : 2 * η ≤ D)
    (ha : 0 ≤ a) (hI : 2 * a * (E / η) ≤ I) :
    (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 * (E / η) ≤
      (u ^ 2 * (E / η) - u ^ 2 * (E / D)) + I := by sorry
