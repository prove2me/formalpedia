-- Prove2me | Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sum
-- name    : ThreeSum.MaskDifference.subsetMask_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:20.595718+00:00
-- url     : https://prove2.me/theorems/3d35230d-87d3-4ff3-a736-5a0795a58fc4
-- title:
--   Mask Difference: subset Mask sum
-- statement:
--   The Mask Difference construction uses the subset Mask sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L9-L11
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskDifference.lean#L9-L11

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress

theorem ThreeSum.MaskDifference.subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by sorry
