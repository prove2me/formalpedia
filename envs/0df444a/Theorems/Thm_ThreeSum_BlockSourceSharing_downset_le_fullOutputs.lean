-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_downset_le_fullOutputs
-- name    : ThreeSum.BlockSourceSharing.downset_le_fullOutputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:23.483336+00:00
-- url     : https://prove2.me/theorems/6e40ce5a-a23e-4bc0-b160-fb2b8fb80ec1
-- title:
--   Block Source Sharing: downset le full Outputs
-- statement:
--   The Block Source Sharing construction uses the downset le full Outputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L68-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L68-L70

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

theorem ThreeSum.BlockSourceSharing.downset_le_fullOutputs (n : ℕ) :
    downsetCap (256*mu n) (mu n) ≤ (mu n+1)*fullOutputs n := by sorry
