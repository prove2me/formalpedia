-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentBatch_Procs_meets
-- name    : ThreeSum.LightTernaryMomentBatch.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:20.121579+00:00
-- url     : https://prove2.me/theorems/2a485563-5857-441a-b606-fda3091b196d
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentBatch.lean#L55-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentBatch.lean#L55-L153

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentBatch
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentRow_Procs_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryMomentBatch
open Light FiniteMomentZeroDetector
attribute [local instance] Classical.propDecidable
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentBatch.Procs.meets {H pMain : ℕ} (S : Procs H P pMain)
    {μ : ℕ→ℤ} {records count originalA originalCount matrix scratch U : ℕ}
    (position t : ℕ→ℕ) (A : ℕ→ℤ) (v w : ∀ i, Fin (t i)→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hrecords : records+3*count≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hpositions : ∀ i<count, position i<originalCount)
    (hpositionRead : ∀ i<count, μ (records+3*i)=(position i : ℤ))
    (hAread : ∀ j<originalCount, μ (originalA+j)=A j)
    (hA : ∀ j<originalCount, |A j|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hv : ∀ i<count, Function.Injective (v i))
    (hweights : ∀ i<count, ∀ s, w i s≠0) (ht : ∀ i<count, t i≤H)
    (hmabs : ∀ i<count, ∀ k≤2*H, |moment (v i) (w i) k|≤(U : ℤ))
    (hm : ∀ i<count, ∀ k≤2*H, μ (matrix+k*count+i)=moment (v i) (w i) k) :
    Meets lim P pMain d [records,count,originalA,originalCount,matrix,scratch] μ (time H count)
      (fun r ν => r=(if ∃ i<count, ∃ s, v i s=A (position i) then 1 else 0 : ℤ) ∧
        Kept μ ν scratch) := by sorry
