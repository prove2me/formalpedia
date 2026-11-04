-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankStages_inverse_program_meets
-- name    : ThreeSum.LightWeightedBankStages.inverse_program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:09.184117+00:00
-- url     : https://prove2.me/theorems/cbafb386-6d64-4e83-9f15-b0561b03f3f2
-- title:
--   Light Weighted Bank Stages: inverse program meets
-- statement:
--   The Light Weighted Bank Stages construction uses the inverse program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L151-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankStages.lean#L151-L171

import Definitions.Def_Submission_Weighted_BankSweep
import Definitions.Def_Submission_Weighted_BankStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedBankStages.inverse_program_meets {N T n a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (H : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=H (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hH : ∀ R, |H R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim (program true) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => stageValue s H) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by sorry
