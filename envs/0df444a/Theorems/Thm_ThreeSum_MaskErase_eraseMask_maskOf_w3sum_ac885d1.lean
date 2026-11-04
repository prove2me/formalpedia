-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf_w3sum_ac885d1
-- name    : ThreeSum.MaskErase.eraseMask_maskOf_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:59.59712+00:00
-- url     : https://prove2.me/theorems/34bab79a-bbd6-4f1e-a092-3a9505e250e6
-- title:
--   Mask Erase: erase Mask mask Of
-- statement:
--   The Mask Erase construction uses the erase Mask mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L43-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L43-L74

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress

theorem ThreeSum.MaskErase.eraseMask_maskOf_w3sum_ac885d1 {L : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.range L) (a : ℕ) :
    eraseMask L a (maskOf s) = maskOf (s.erase a) := by sorry
