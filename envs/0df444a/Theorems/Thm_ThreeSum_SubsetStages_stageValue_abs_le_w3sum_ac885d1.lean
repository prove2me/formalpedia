-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le_w3sum_ac885d1
-- name    : ThreeSum.SubsetStages.stageValue_abs_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:09.403895+00:00
-- url     : https://prove2.me/theorems/65b94839-bf70-43d9-a21f-9d5c8b7e4754
-- title:
--   Subset Stages: stage Value abs le
-- statement:
--   The absolute bound is derived from the original input values; no bound
--   on any intermediate transform is supplied as an extra assumption.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L66-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L66-L88

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.stageValue_abs_le_w3sum_ac885d1 {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by sorry
