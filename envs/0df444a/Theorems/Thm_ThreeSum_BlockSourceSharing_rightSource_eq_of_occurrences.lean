-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceSharing_rightSource_eq_of_occurrences
-- name    : ThreeSum.BlockSourceSharing.rightSource_eq_of_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:51.768453+00:00
-- url     : https://prove2.me/theorems/f891d57e-1288-4505-9621-e73d55d27f9f
-- title:
--   Block Source Sharing: right Source eq of occurrences
-- statement:
--   The Block Source Sharing construction uses the right Source eq of occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L28-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceSharing.lean#L28-L33

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

theorem ThreeSum.BlockSourceSharing.rightSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    rightSource P d B b q = rightSource P d B b q' := by sorry
