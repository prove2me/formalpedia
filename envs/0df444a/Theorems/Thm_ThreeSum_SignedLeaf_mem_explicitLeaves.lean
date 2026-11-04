-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitLeaves
-- name    : ThreeSum.SignedLeaf.mem_explicitLeaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:02.067784+00:00
-- url     : https://prove2.me/theorems/0a8abe12-6e74-46db-9fb9-d6397f811047
-- title:
--   Signed Leaf: mem explicit Leaves
-- statement:
--   The Signed Leaf construction uses the mem explicit Leaves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L97-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L97-L106

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.mem_explicitLeaves {W : ℕ} (Q S : Finset (Fin W)) (t : ℕ) :
    S ∈ explicitLeaves Q t ↔ S ⊆ Q ∧ (Q \ S).card < t := by sorry
