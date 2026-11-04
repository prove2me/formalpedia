-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_stageValue_abs_le_w3sum_ac885d1
-- name    : ThreeSum.BoxStages.stageValue_abs_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:37.668206+00:00
-- url     : https://prove2.me/theorems/ebc3407b-7c59-42a6-9dee-747158d630f1
-- title:
--   Box Stages: stage Value abs le
-- statement:
--   The Box Stages construction uses the stage Value abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L61-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BoxStages.lean#L61-L83

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_WeightedCache3SUM_Alias_8b6c5b6059fc82de

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset

theorem ThreeSum.BoxStages.stageValue_abs_le_w3sum_ac885d1 {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by sorry
