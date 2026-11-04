-- Prove2me | Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_notMem
-- name    : ThreeSum.MaskUnion.scanSet_succ_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:03.827286+00:00
-- url     : https://prove2.me/theorems/45351726-52f0-4c82-b2e1-ebc7a6afe9ab
-- title:
--   Mask Union: scan Set succ not Mem
-- statement:
--   The Mask Union construction uses the scan Set succ not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L28-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L28-L33

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskUnion.scanSet_succ_notMem {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∉ B) : scanSet A B (j+1) = scanSet A B j := by sorry
