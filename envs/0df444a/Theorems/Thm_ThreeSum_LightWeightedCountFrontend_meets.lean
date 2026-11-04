-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCountFrontend_meets
-- name    : ThreeSum.LightWeightedCountFrontend.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:12:25.090932+00:00
-- url     : https://prove2.me/theorems/0cb9a916-e3a8-4f5e-a075-0417fbdf4904
-- title:
--   Light Weighted Count Frontend: meets
-- statement:
--   The Light Weighted Count Frontend construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountFrontend.lean#L61-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountFrontend.lean#L61-L171

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_Weighted_GroupBankResources
import Definitions.Def_Submission_Weighted_WantedRows
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

theorem ThreeSum.LightWeightedCountFrontend.meets {lim : Limits} {N bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst d V t : ℕ}
    (f g : Config) (Qstar : TritWord N) (Q : ℕ→TritWord N) (group : ℕ→ℕ)
    (F G : ℕ→TritWord N→ℤ) (E : Enumeration N f.T f.nb) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : f.bank+f.nb≤keyBase) (hfs : fsource+groups*f.nb≤keyBase) (hgs : gsource+groups*f.nb≤keyBase)
    (hmeta : keyBase+4*f.nb≤bankPowers) (hpows : bankPowers+(2*N+1)≤fbase)
    (hfg : fbase+groups*((N+1)*f.nb)≤gbase) (hgh : gbase+groups*((N+1)*f.nb)≤hbase)
    (hHdst : hbase+groups*((N+1)*f.nb)≤dst)
    (hword : ((f.nb+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hgroupsWord : (groups : ℤ)+1≤lim.word)
    (hcodes : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ g<groups, ∀ j<f.nb, μ (fsource+g*f.nb+j)=F g (E.word j))
    (hsourceG : ∀ g<groups, ∀ j<f.nb, μ (gsource+g*f.nb+j)=G g (E.word j))
    (hsorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k))
    (hF : ∀ g<groups, ∀ R, |F g R|≤(V : ℤ)) (hG : ∀ g<groups, ∀ R, |G g R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightWeightedBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightWeightedBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : f.L≤2*N) (hn : f.nb<2^f.L)
    (hrecords : records+3*count≤keyBase) (hdst : dst+count≤f.a) (hspace : f.a≤lim.space)
    (hreadGroup : ∀ j<count, μ (records+3*j+2)=(group j : ℤ))
    (hreadQ : ∀ j<count, μ (records+3*j+1)=(address (Q j) : ℤ))
    (hgroup : ∀ j<count, group j<groups) (hRank : ∀ j<count, cacheCost (Q j)=cacheCost Qstar)
    (hcountWord : (count : ℤ)+1≤lim.word)
    (hstrideWord : (((N+1)*f.nb : ℕ) : ℤ)≤lim.word) (htailWord : ((N*f.nb : ℕ) : ℤ)≤lim.word)
    (hplan : ∀ j<count, Plan lim out (hbase+group j*((N+1)*f.nb)) caps
      (sourceConfig f fbase ((N+1)*f.nb) (N*f.nb) (group j))
      (sourceConfig g gbase ((N+1)*f.nb) (N*f.nb) (group j))
      (Q j) E (F (group j)) (G (group j)))
    (htime : ∀ j<count, LightWeightedPreparedWanted.time
      (sourceConfig f fbase ((N+1)*f.nb) (N*f.nb) (group j))
      (sourceConfig g gbase ((N+1)*f.nb) (N*f.nb) (group j)) (Q j)≤t)
    (hd : d+3*N+f.L+16≤lim.depth) :
    Meets lim program 63 d
      (args f g Qstar bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst)
      μ (time groups N f.L f.nb count t)
      (fun _ ν => Kept μ ν keyBase ∧ ∀ j<count, ν (dst+j)=LightWeightedWantedRows.score F G group Q j) := by sorry
