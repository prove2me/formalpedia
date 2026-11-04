-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_product_values_mem_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.product_values_mem_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:56.027387+00:00
-- url     : https://prove2.me/theorems/a5e05fdc-8172-4935-8032-53e851f0c0be
-- title:
--   Band Raw A: product values mem
-- statement:
--   The Band Raw A construction uses the product values mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L27-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L27-L41

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.product_values_mem_w3sum_ac885d1 {A B C : List ℤ} {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ A ∧
      B.getD t.2.1 0 ∈ B ∧ C.getD t.2.2 0 ∈ C := by sorry
