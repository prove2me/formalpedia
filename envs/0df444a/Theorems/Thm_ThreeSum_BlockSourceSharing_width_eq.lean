-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
-- name    : ThreeSum.BlockSourceSharing.width_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:17.150881+00:00
-- url     : https://prove2.me/theorems/5592cb4b-09d5-41f1-b253-001347b84722
-- title:
--   Block Source Sharing: width eq
-- statement:
--   The Block Source Sharing construction uses the width eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L58-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L58-L61

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds

theorem ThreeSum.BlockSourceSharing.width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by sorry
