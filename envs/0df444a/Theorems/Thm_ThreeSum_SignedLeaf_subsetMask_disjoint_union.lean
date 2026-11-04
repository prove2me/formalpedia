-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_subsetMask_disjoint_union
-- name    : ThreeSum.SignedLeaf.subsetMask_disjoint_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:16.530822+00:00
-- url     : https://prove2.me/theorems/91c88e5e-56bb-4119-aa25-b6261f78c4ef
-- title:
--   Signed Leaf: subset Mask disjoint union
-- statement:
--   Union of disjoint coordinate masks is ordinary integer addition.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L18-L20

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.subsetMask_disjoint_union {W : ℕ} (A B : Finset (Fin W)) (hd : Disjoint A B) :
    subsetMask (A ∪ B) = subsetMask A+subsetMask B := by sorry
