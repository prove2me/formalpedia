-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentRow_Procs_meets
-- name    : ThreeSum.LightTernaryMomentRow.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:30.216357+00:00
-- url     : https://prove2.me/theorems/bd8c6562-9375-4d64-8a35-dae4878afa76
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentRow.lean#L27-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentRow.lean#L27-L74

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryMomentRow
open Light FiniteMomentZeroDetector
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentRow.Procs.meets {H pMain : ℕ} (S : Procs H P pMain)
    {μ : ℕ→ℤ} {record originalA originalCount matrix count row scratch position U t : ℕ}
    (a : ℤ) (v w : Fin t→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hr : row<count) (hpos : position<originalCount)
    (hrecord : record+3≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hposition : μ record=(position : ℤ)) (hAread : μ (originalA+position)=a)
    (ha : |a|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hv : Function.Injective v) (hweights : ∀ s, w s≠0) (ht : t≤H)
    (hmabs : ∀ k≤2*H, |moment v w k|≤(U : ℤ))
    (hm : ∀ k≤2*H, μ (matrix+k*count+row)=moment v w k) :
    Meets lim P pMain d [record,originalA,originalCount,matrix,count,row,scratch] μ (time H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ Kept μ ν scratch) := by sorry
