-- Prove2me | Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_mem
-- name    : ThreeSum.MaskUnion.scanSet_succ_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:32.155183+00:00
-- url     : https://prove2.me/theorems/0f0b7f04-ebdd-42ab-8265-0d37ccbdc61d
-- title:
--   Mask Union: scan Set succ mem
-- statement:
--   The Mask Union construction uses the scan Set succ mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L20-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L20-L26

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskUnion.scanSet_succ_mem {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) :
    scanSet A B (j+1) = insert ⟨j,hj⟩ (scanSet A B j) := by sorry
