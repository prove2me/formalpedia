-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_neg_one_pow_sub
-- name    : ThreeSum.SignedLeaf.neg_one_pow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:16.206956+00:00
-- url     : https://prove2.me/theorems/dfe3aa2b-0cad-4dfe-a65c-233d443b3b31
-- title:
--   Signed Leaf: neg one pow sub
-- statement:
--   The Signed Leaf construction uses the neg one pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L38-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L38-L44

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ)^(a-b) = (-1 : ℤ)^a*(-1 : ℤ)^b := by sorry
