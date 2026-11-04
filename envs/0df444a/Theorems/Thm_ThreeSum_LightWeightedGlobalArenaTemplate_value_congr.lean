-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalArenaTemplate_value_congr
-- name    : ThreeSum.LightWeightedGlobalArenaTemplate.value_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:59:25.50401+00:00
-- url     : https://prove2.me/theorems/323df0e4-1ee8-4a8c-b692-5700710215d0
-- title:
--   Light Weighted Global Arena Template: value congr
-- statement:
--   The Light Weighted Global Arena Template construction uses the value congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L182-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean#L182-L192

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalArenaTemplate.value_congr {loc initial : ℕ → ℤ} {free C : ℕ}
    (hread : ∀ i<23, loc i=initial i) (f : Field) (hg : Good f) :
    value loc free C f=value initial free C f := by sorry
