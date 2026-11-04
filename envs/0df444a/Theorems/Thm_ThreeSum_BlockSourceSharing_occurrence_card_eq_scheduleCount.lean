-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_occurrence_card_eq_scheduleCount
-- name    : ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:40.824052+00:00
-- url     : https://prove2.me/theorems/ef630031-2698-4c19-b1ae-879a275d324e
-- title:
--   Block Source Sharing: occurrence card eq schedule Count
-- statement:
--   The Block Source Sharing construction uses the occurrence card eq schedule Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L54-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L54-L56

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

theorem ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by sorry
