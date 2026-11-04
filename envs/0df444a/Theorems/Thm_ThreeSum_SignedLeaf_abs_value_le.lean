-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le
-- name    : ThreeSum.SignedLeaf.abs_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:03.259824+00:00
-- url     : https://prove2.me/theorems/2d2495ce-050d-492f-8f12-b6a941a8ef17
-- title:
--   Signed Leaf: abs value le
-- statement:
--   The Signed Leaf construction uses the abs value le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L27-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L27-L36

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by sorry
