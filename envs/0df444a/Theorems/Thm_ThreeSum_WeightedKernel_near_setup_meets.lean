-- Prove2me | Theorems.Thm_ThreeSum_WeightedKernel_near_setup_meets
-- name    : ThreeSum.WeightedKernel.near_setup_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:43.08392+00:00
-- url     : https://prove2.me/theorems/7063e265-2e46-4b35-9e74-426f82fb4225
-- title:
--   Weighted Kernel: near setup meets
-- statement:
--   The Weighted Kernel construction uses the near setup meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/KernelProgram.lean#L196-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/KernelProgram.lean#L196-L213

import Definitions.Def_Submission_Weighted_NearSourceWords
import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_NearSetup
import Definitions.Def_Submission_Weighted_KernelProgram
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.WeightedKernel.near_setup_meets {N D dst powers caps active d : ℕ}
    (μ : ℕ → ℤ) (Q : TritWord N)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ)≤lim.word)
    (hcontrol : ((1025*N+1100 : ℕ) : ℤ)≤lim.word)
    (hD : D≤1025*N)
    (hdst : dst+(WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).length≤caps)
    (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hd : d+2*N+3≤lim.depth) :
    Meets lim program 37 d [N,D,address Q,dst,powers,caps,active] μ (LightWeightedNearSetup.time Q D)
      (fun r ν => r=((WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).length : ℤ) ∧
        Seg ν dst ((WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).map (fun c => (c : ℤ))) ∧
        Powers ν powers (2*N) ∧ (∀ i<N, ν (active+i)=1) ∧ Kept μ ν dst) := by sorry
