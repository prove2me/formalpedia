-- Prove2me | Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff
-- name    : ThreeSum.MaskDifference.subsetMask_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:38.77891+00:00
-- url     : https://prove2.me/theorems/9d25195d-516b-4e57-be05-cc2d8ccff8b4
-- title:
--   Mask Difference: subset Mask sdiff
-- statement:
--   The Mask Difference construction uses the subset Mask sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L46-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L46-L49

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskDifference.subsetMask_sdiff {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask Q-subsetMask U = subsetMask (Q \ U) := by sorry
