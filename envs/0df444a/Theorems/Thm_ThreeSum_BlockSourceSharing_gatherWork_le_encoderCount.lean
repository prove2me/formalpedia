-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_gatherWork_le_encoderCount
-- name    : ThreeSum.BlockSourceSharing.gatherWork_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:42.453194+00:00
-- url     : https://prove2.me/theorems/633b9c54-9ecf-457f-a91c-d3631792e0ae
-- title:
--   Block Source Sharing: gather Work le encoder Count
-- statement:
--   The Block Source Sharing construction uses the gather Work le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L109-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L109-L125

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

theorem ThreeSum.BlockSourceSharing.gatherWork_le_encoderCount (n E : ℕ) :
    gatherWork n E ≤ 326*(256*mu n+1)*(Nat.log 2 (E+1)+1)*encoderCount n := by sorry
