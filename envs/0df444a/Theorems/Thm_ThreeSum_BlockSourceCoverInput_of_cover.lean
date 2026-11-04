-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCoverInput_of_cover
-- name    : ThreeSum.BlockSourceCoverInput.of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:28.54832+00:00
-- url     : https://prove2.me/theorems/bb4e03de-1b7e-43e1-8b93-084339b7f9df
-- title:
--   Block Source Cover Input: of cover
-- statement:
--   The Block Source Cover Input construction uses the of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCoverInput.lean#L29-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCoverInput.lean#L29-L43

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCoverInput
open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags

theorem ThreeSum.BlockSourceCoverInput.of_cover {μ : ℕ → ℤ} {h allMaps matrix maps candidates histL histR : ℕ}
    (H : LightLocalCoverTables.Data μ h allMaps histL histR matrix)
    (R : LightLocalCoverTables.ScheduleRows μ h maps)
    (I : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)) :
    Input μ h maps candidates histL histR := by sorry
