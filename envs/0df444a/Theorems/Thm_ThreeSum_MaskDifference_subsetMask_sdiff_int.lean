-- Prove2me | Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff_int
-- name    : ThreeSum.MaskDifference.subsetMask_sdiff_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:37.624606+00:00
-- url     : https://prove2.me/theorems/54ade9b2-87e3-4a1e-811e-2251cd406fe3
-- title:
--   Mask Difference: subset Mask sdiff int
-- statement:
--   The Mask Difference construction uses the subset Mask sdiff int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L51-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L51-L56

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskDifference.subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by sorry
