-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_relevant_product_complete_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.relevant_product_complete_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:15.432053+00:00
-- url     : https://prove2.me/theorems/b5778e1d-48f4-4cb1-acb3-d1f9aa6a7c50
-- title:
--   Band Raw A: relevant product complete
-- statement:
--   Every relevant original owner contributes all coordinates of its
--   actual band product. The returned A index is the physical flattened one.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L154-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L154-L178

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.relevant_product_complete_w3sum_ac885d1 {A B C : BandEnumeration.Family}
    {nA nB nC g pA pB pC : ℕ} (t : BandEnumeration.Triple A B C)
    (ht : BandEnumeration.relevant A B C t)
    (ha : BandPartition.start g t.1.val ≤ pA ∧ pA < BandPartition.stop nA g t.1.val)
    (hb : BandPartition.start g t.2.1.val ≤ pB ∧ pB < BandPartition.stop nB g t.2.1.val)
    (hc : BandPartition.start g t.2.2.val ≤ pC ∧ pC < BandPartition.stop nC g t.2.2.val) :
    ∃ k < (items nA g (records A B C)).length,
      labelAt nA g (records A B C) k=⟨slot A B C (BandEnumeration.owner A B C t),pA⟩ ∧
      (k,pB,pC) ∈ ownerProduct nA nB nC g (records A B C)
        (slot A B C (BandEnumeration.owner A B C t)) := by sorry
