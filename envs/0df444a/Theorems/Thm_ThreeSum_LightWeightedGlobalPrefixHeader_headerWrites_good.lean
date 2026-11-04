-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_headerWrites_good
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:18.128912+00:00
-- url     : https://prove2.me/theorems/e3cb7e18-6656-4d34-90f0-026df0152ae3
-- title:
--   Light Weighted Global Prefix Header: header Writes good
-- statement:
--   The Light Weighted Global Prefix Header construction uses the header Writes good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L75-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L75-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_good : ∀ir∈headerWrites, ir.1<106 ∧ ir.2<30 := by sorry
