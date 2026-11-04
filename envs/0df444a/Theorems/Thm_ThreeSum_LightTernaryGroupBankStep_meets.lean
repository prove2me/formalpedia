-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_meets
-- name    : ThreeSum.LightTernaryGroupBankStep.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:36.545207+00:00
-- url     : https://prove2.me/theorems/a0a0680b-cf3d-498e-9d7e-d615e859bb19
-- title:
--   Light Ternary Group Bank Step: meets
-- statement:
--   The Light Ternary Group Bank Step construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankStep.lean#L23-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankStep.lean#L23-L84

import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryGroupBankStep.meets {tail : Program} {pMain pCopy N T n a powers L keyBase fsource gsource fbase gbase hbase d V : ℕ}
    (hmain : (LightTernaryBankAssembly.program++tail)[pMain]?=some (body pCopy))
    (hcopy : (LightTernaryBankAssembly.program++tail)[pCopy]?=some copyBody)
    (E : Enumeration N T n) (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hfs : fsource+n≤keyBase) (hgs : gsource+n≤keyBase)
    (hmeta : keyBase+4*n≤powers) (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+(N+1)*n≤gbase) (hgh : gbase+(N+1)*n≤hbase)
    (hspace : hbase+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ j<n, μ (fsource+j)=F (E.word j))
    (hsourceG : ∀ j<n, μ (gsource+j)=G (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightTernaryBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightTernaryBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+7≤lim.depth) :
    Meets lim (LightTernaryBankAssembly.program++tail) pMain d
      [N,a,n,powers,L,keyBase,fsource,gsource,fbase,gbase,hbase] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) fbase N μ' ∧
        Stages E (fun s => forwardStage s G) gbase N μ' ∧
        Stages E (fun s => stageValue s (LightTernaryBankAssembly.product F G)) hbase N μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2*N)) := by sorry
