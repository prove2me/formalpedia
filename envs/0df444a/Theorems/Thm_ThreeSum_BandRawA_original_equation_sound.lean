-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_original_equation_sound
-- name    : ThreeSum.BandRawA.original_equation_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:50.775838+00:00
-- url     : https://prove2.me/theorems/66180a1a-0cdd-4820-b76e-ad4bd9930ff7
-- title:
--   Band Raw A: original equation sound
-- statement:
--   The Band Raw A construction uses the original equation sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L106-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAOriginal.lean#L106-L114

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1+B.getD t.2.1 0=C.getD t.2.2 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c := by sorry
