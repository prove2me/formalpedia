-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_headerWrites_nodup
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:23.133914+00:00
-- url     : https://prove2.me/theorems/97d3f55a-33fd-4f28-9435-66459c397581
-- title:
--   Light Weighted Global Prefix Header: header Writes nodup
-- statement:
--   The Light Weighted Global Prefix Header construction uses the header Writes nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L76-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L76-L76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.headerWrites_nodup : (headerWrites.map Prod.fst).Nodup := by sorry
