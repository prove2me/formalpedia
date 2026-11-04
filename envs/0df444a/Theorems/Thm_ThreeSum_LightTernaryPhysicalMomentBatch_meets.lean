-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPhysicalMomentBatch_meets
-- name    : ThreeSum.LightTernaryPhysicalMomentBatch.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:32.801606+00:00
-- url     : https://prove2.me/theorems/918d9454-0321-47ce-bf99-06d647359d6b
-- title:
--   Light Ternary Physical Moment Batch: meets
-- statement:
--   The Light Ternary Physical Moment Batch construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPhysicalMomentBatch.lean#L14-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPhysicalMomentBatch.lean#L14-L62

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentBatch_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentRow_Procs_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPhysicalMomentBatch
open Light TernaryPhysicalMomentSupport FiniteMomentZeroDetector
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryPhysicalMomentBatch.meets {H pMain records count originalA originalCount matrix scratch U : ℕ}
    (S : LightTernaryMomentBatch.Procs H P pMain)
    (Pair : ℕ→Type*) [∀ i, Fintype (Pair i)]
    (mode mass : ∀ i, Pair i→ℤ) (position : ℕ→ℕ) (A : ℕ→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hrecords : records+3*count≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hpositions : ∀ i<count, position i<originalCount)
    (hpositionRead : ∀ i<count, μ (records+3*i)=(position i : ℤ))
    (hAread : ∀ j<originalCount, μ (originalA+j)=A j)
    (hA : ∀ j<originalCount, |A j|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hpositive : ∀ i<count, ∀ a, 0<mass i a)
    (hsupport : ∀ i<count, (support (mode i)).card≤H)
    (hmabs : ∀ i<count, ∀ k≤2*H, |∑ a, mass i a*mode i a^k|≤(U : ℤ))
    (hm : ∀ i<count, ∀ k≤2*H, μ (matrix+k*count+i)=∑ a, mass i a*mode i a^k) :
    Meets lim P pMain d [records,count,originalA,originalCount,matrix,scratch] μ
      (LightTernaryMomentBatch.time H count)
      (fun r ν => r=(if ∃ i<count, ∃ a, mode i a=A (position i) then 1 else 0 : ℤ) ∧
        Kept μ ν scratch) := by sorry
