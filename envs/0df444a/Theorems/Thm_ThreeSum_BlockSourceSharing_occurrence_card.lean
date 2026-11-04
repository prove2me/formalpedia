-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_occurrence_card
-- name    : ThreeSum.BlockSourceSharing.occurrence_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:29.981075+00:00
-- url     : https://prove2.me/theorems/aa28d011-8a22-4f7c-864a-9253f5d3dc10
-- title:
--   Block Source Sharing: occurrence card
-- statement:
--   The Block Source Sharing construction uses the occurrence card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L51-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L51-L52

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

theorem ThreeSum.BlockSourceSharing.occurrence_card (h J : ℕ) : Fintype.card (Occurrences h J) = scheduleSize h^J := by sorry
