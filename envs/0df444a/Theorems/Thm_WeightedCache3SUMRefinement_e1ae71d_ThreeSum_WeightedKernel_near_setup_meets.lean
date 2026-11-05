-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedKernel_near_setup_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.near_setup_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:31:37.601605+00:00
-- url     : https://prove2.me/theorems/03602458-56f5-4e4c-ba60-912d9cb9f3d8
-- title:
--   near_setup_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L196-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L196-L213

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.near_setup_meets {N D dst powers caps active d : ℕ}
    (μ : ℕ → ℤ) (Q : TritWord N)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ)≤lim.word)
    (hcontrol : ((2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hD : D≤2740*N)
    (hdst : dst+(WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).length≤caps)
    (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hd : d+2*N+3≤lim.depth) :
    Meets lim program 37 d [N,D,address Q,dst,powers,caps,active] μ (LightWeightedNearSetup.time Q D)
      (fun r ν => r=((WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).length : ℤ) ∧
        Seg ν dst ((WeightedNearEnumeration.codes (WeightedBankEnumeration.wordList Q) D).map (fun c => (c : ℤ))) ∧
        Powers ν powers (2*N) ∧ (∀ i<N, ν (active+i)=1) ∧ Kept μ ν dst) := by sorry
