-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedKernel_bank_zeta_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.bank_zeta_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:30:30.428276+00:00
-- url     : https://prove2.me/theorems/2437dea5-b4ef-41e3-a37c-869f398faeb5
-- title:
--   bank_zeta_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L104-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/KernelProgram.lean#L104-L124

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.bank_zeta_meets {N T n
    a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim program 18 d [N,a,n,powers,L,keyBase,base] μ (LightWeightedBankSweep.time N L n)
      (fun _ μ' => LightWeightedBankSweep.Stages E (fun s => forwardStage s F) base N μ' ∧
        LightWeightedBankSweep.Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
