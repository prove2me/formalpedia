-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_cutoff_eq
-- name    : ThreeSum.BlockSourceSharing.cutoff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:40.74785+00:00
-- url     : https://prove2.me/theorems/e6fc291e-92a6-4877-bb3b-7eed8943cfc4
-- title:
--   Block Source Sharing: cutoff eq
-- statement:
--   The Block Source Sharing construction uses the cutoff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L63-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L63-L66

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

theorem ThreeSum.BlockSourceSharing.cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by sorry
