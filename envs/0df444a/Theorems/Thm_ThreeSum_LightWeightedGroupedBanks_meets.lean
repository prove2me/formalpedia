-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
-- name    : ThreeSum.LightWeightedGroupedBanks.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:59.978014+00:00
-- url     : https://prove2.me/theorems/91b14a67-1c06-40b9-b0ab-b9c24d2fdcf6
-- title:
--   Light Weighted Grouped Banks: meets
-- statement:
--   The Light Weighted Grouped Banks construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupedBanks.lean#L52-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupedBanks.lean#L52-L200

import Definitions.Def_Submission_Weighted_GroupBankStep
import Definitions.Def_Submission_Weighted_GroupedBanks
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGroupedBanks.meets {N T n a powers L keyBase groups fsource gsource fbase gbase hbase d V : ℕ}
    (E : Enumeration N T n) (F G : ℕ→TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hfs : fsource+groups*n≤keyBase) (hgs : gsource+groups*n≤keyBase)
    (hmeta : keyBase+4*n≤powers) (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+groups*((N+1)*n)≤gbase) (hgh : gbase+groups*((N+1)*n)≤hbase)
    (hspace : hbase+groups*((N+1)*n)≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hgroupsWord : (groups : ℤ)+1≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ g<groups, ∀ j<n, μ (fsource+g*n+j)=F g (E.word j))
    (hsourceG : ∀ g<groups, ∀ j<n, μ (gsource+g*n+j)=G g (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ g<groups, ∀ R, |F g R|≤(V : ℤ)) (hG : ∀ g<groups, ∀ R, |G g R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightWeightedBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightWeightedBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+8≤lim.depth) :
    Meets lim program 19 d [N,a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase] μ
      (time groups N L n)
      (fun _ μ' => GroupStages E (fun g s => forwardStage s (F g)) fbase groups μ' ∧
        GroupStages E (fun g s => forwardStage s (G g)) gbase groups μ' ∧
        GroupStages E (fun g s => stageValue s (LightWeightedBankAssembly.product (F g) (G g))) hbase groups μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N groups ∧ Powers μ' powers (2*N)) := by sorry
