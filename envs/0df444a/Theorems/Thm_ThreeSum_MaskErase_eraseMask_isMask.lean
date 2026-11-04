-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_isMask
-- name    : ThreeSum.MaskErase.eraseMask_isMask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:07.222453+00:00
-- url     : https://prove2.me/theorems/1fed072c-0bec-496b-941e-cec464577950
-- title:
--   Mask Erase: erase Mask is Mask
-- statement:
--   The Mask Erase construction uses the erase Mask is Mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L95-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L95-L98

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress

theorem ThreeSum.MaskErase.eraseMask_isMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) (ha : a ∈ s) :
    IsMask L (s.card-1) (eraseMask L a.val (subsetMask s)) := by sorry
