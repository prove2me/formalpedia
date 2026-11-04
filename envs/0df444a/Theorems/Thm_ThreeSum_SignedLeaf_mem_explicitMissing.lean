-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
-- name    : ThreeSum.SignedLeaf.mem_explicitMissing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:19.202561+00:00
-- url     : https://prove2.me/theorems/da56e9e3-9dfa-414e-837d-eef717e0f3ce
-- title:
--   Signed Leaf: mem explicit Missing
-- statement:
--   The Signed Leaf construction uses the mem explicit Missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L65-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L65-L72

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.mem_explicitMissing {W : ℕ} (Q U : Finset (Fin W)) (t : ℕ) :
    U ∈ explicitMissing Q t ↔ U ⊆ Q ∧ U.card < t := by sorry
