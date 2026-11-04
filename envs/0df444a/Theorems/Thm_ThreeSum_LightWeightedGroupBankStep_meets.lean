-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
-- name    : ThreeSum.LightWeightedGroupBankStep.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:35.263716+00:00
-- url     : https://prove2.me/theorems/792be068-7eb5-47a1-8b48-f98945a1b184
-- title:
--   Light Weighted Group Bank Step: meets
-- statement:
--   The Light Weighted Group Bank Step construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankStep.lean#L28-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankStep.lean#L28-L89

import Definitions.Def_Submission_Weighted_BankResources
import Definitions.Def_Submission_Weighted_GroupBankStep
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGroupBankStep.meets {tail : Program} {pMain pCopy N T n a powers L keyBase fsource gsource fbase gbase hbase d V : ℕ}
    (hmain : (LightWeightedBankAssembly.program++tail)[pMain]?=some (body pCopy))
    (hcopy : (LightWeightedBankAssembly.program++tail)[pCopy]?=some copyBody)
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
    (hproductWord : (LightWeightedBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightWeightedBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+7≤lim.depth) :
    Meets lim (LightWeightedBankAssembly.program++tail) pMain d
      [N,a,n,powers,L,keyBase,fsource,gsource,fbase,gbase,hbase] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) fbase N μ' ∧
        Stages E (fun s => forwardStage s G) gbase N μ' ∧
        Stages E (fun s => stageValue s (LightWeightedBankAssembly.product F G)) hbase N μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2*N)) := by sorry
