-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_resultHeader_length
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.resultHeader_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:08.476613+00:00
-- url     : https://prove2.me/theorems/29316043-6a4e-4621-a83c-288bdc608ba7
-- title:
--   Light Weighted Global Prefix Header: result Header length
-- statement:
--   The Light Weighted Global Prefix Header construction uses the result Header length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L49-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L49-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.resultHeader_length (xs : List ℤ)
    (template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase : ℕ)
    (ret : ℤ) :
    (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J N T L groups nb bank powers Fbase Gbase ret).length=xs.length := by sorry
