-- Prove2me | Theorems.Thm_ThreeSum_SignedLeaf_mobius_eq_signed_sum
-- name    : ThreeSum.SignedLeaf.mobius_eq_signed_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:06.491012+00:00
-- url     : https://prove2.me/theorems/ffb7b6a2-d37c-4356-b11a-993f1086c9fd
-- title:
--   Signed Leaf: mobius eq signed sum
-- statement:
--   The Signed Leaf construction uses the mobius eq signed sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L46-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SignedLeaf.lean#L46-L56

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.SignedLeaf.mobius_eq_signed_sum {W : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR Q : Finset (Fin W)) :
    Subset.mobius
      (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
        SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, value f g stage preL preR S := by sorry
