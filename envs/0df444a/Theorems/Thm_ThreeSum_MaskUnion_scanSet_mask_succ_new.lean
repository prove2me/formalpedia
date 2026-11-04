-- Prove2me | Theorems.Thm_ThreeSum_MaskUnion_scanSet_mask_succ_new
-- name    : ThreeSum.MaskUnion.scanSet_mask_succ_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:06.677481+00:00
-- url     : https://prove2.me/theorems/e174b5a8-cfb4-4d19-9f3d-3e7af2444a34
-- title:
--   Mask Union: scan Set mask succ new
-- statement:
--   The Mask Union construction uses the scan Set mask succ new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L51-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L51-L57

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskUnion.scanSet_mask_succ_new {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∉ A) :
    subsetMask (scanSet A B (j+1)) = subsetMask (scanSet A B j)+2^j := by sorry
