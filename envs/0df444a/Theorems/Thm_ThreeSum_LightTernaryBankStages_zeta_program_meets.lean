-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankStages_zeta_program_meets
-- name    : ThreeSum.LightTernaryBankStages.zeta_program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:20.607707+00:00
-- url     : https://prove2.me/theorems/b8cf9998-dcca-41b3-9900-39307bec1793
-- title:
--   Light Ternary Bank Stages: zeta program meets
-- statement:
--   The Light Ternary Bank Stages construction uses the zeta program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L124-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankStages.lean#L124-L144

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryBankStages.zeta_program_meets {N T n a powers L keyBase base d V : ℕ}
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
    Meets lim (program false) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
