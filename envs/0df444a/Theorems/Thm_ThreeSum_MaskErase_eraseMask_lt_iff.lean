-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_lt_iff
-- name    : ThreeSum.MaskErase.eraseMask_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:02.790113+00:00
-- url     : https://prove2.me/theorems/618b09f2-ef29-4fb3-bfcb-20d1d3133b57
-- title:
--   Mask Erase: erase Mask lt iff
-- statement:
--   The Mask Erase construction uses the erase Mask lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L89-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L89-L93

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress

theorem ThreeSum.MaskErase.eraseMask_lt_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) < subsetMask s ↔ a ∈ s := by sorry
