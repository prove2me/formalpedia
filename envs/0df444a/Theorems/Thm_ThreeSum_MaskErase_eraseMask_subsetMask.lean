-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_subsetMask
-- name    : ThreeSum.MaskErase.eraseMask_subsetMask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:02.701791+00:00
-- url     : https://prove2.me/theorems/ef99c496-1842-40b8-8edd-d384aea9cf1a
-- title:
--   Mask Erase: erase Mask subset Mask
-- statement:
--   The Mask Erase construction uses the erase Mask subset Mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L80-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L80-L83

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress

theorem ThreeSum.MaskErase.eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) = subsetMask (s.erase a) := by sorry
