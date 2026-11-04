-- Prove2me | Theorems.Thm_ThreeSum_MaskUnion_current_mem_iff
-- name    : ThreeSum.MaskUnion.current_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:40.813818+00:00
-- url     : https://prove2.me/theorems/1a373b4b-0636-43dc-8d9d-e6eec2b52c42
-- title:
--   Mask Union: current mem iff
-- statement:
--   The Mask Union construction uses the current mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L35-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskUnion.lean#L35-L37

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskUnion.current_mem_iff {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W) :
    (⟨j,hj⟩ : Fin W) ∈ scanSet A B j ↔ (⟨j,hj⟩ : Fin W) ∈ A := by sorry
