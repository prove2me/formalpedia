-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
-- name    : ThreeSum.LightTernaryBankAssembly.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:19.241463+00:00
-- url     : https://prove2.me/theorems/86bf80e6-cf85-48dc-892a-eed0bb30500b
-- title:
--   Light Ternary Bank Assembly: meets
-- statement:
--   The Light Ternary Bank Assembly construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L60-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L60-L166

import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryBankAssembly.meets {N T n a powers L keyBase fbase gbase hbase d V : ℕ}
    (E : Enumeration N T n) (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+(N+1)*n≤gbase) (hgh : gbase+(N+1)*n≤hbase)
    (hspace : hbase+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ j<n, μ (fbase+j)=F (E.word j))
    (hsourceG : ∀ j<n, μ (gbase+j)=G (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+6≤lim.depth) :
    Meets lim program 0 d [N,a,n,powers,L,keyBase,fbase,gbase,hbase] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) fbase N μ' ∧
        Stages E (fun s => forwardStage s G) gbase N μ' ∧
        Stages E (fun s => stageValue s (product F G)) hbase N μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2*N)) := by sorry
