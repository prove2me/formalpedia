-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedRowDispatch_meets
-- name    : ThreeSum.LightTernaryWantedRowDispatch.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:46:51.98573+00:00
-- url     : https://prove2.me/theorems/8535bea0-8017-442c-904e-a3504ab3a505
-- title:
--   Light Ternary Wanted Row Dispatch: meets
-- statement:
--   Dispatch executes a proved prepared-query call at the bank addresses read
--   from the actual row's map group, then stores its literal result. This lemma is
--   used with `LightTernaryPreparedWanted.meets` in the row-loop instantiation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedRowDispatch.lean#L35-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedRowDispatch.lean#L35-L67

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRowDispatch
import Theorems.Thm_Light_LocalsBut_update
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedRowDispatch
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedRowDispatch.meets {pMain pPrepare N out bankValues caps record dst fbase gbase hbase stride tail group d t : ℕ}
    (hmain : P[pMain]?=some (body pPrepare))
    (f g : Config) (Qstar Q : TritWord N) (μ : ℕ→ℤ) (value : ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hrecord : record+3≤lim.space) (hdst : dst<lim.space)
    (hreadGroup : μ (record+2)=(group : ℤ)) (hreadQ : μ (record+1)=(address Q : ℤ))
    (hgroupWord : (group : ℤ)≤lim.word) (hcodeWord : (address Q : ℤ)≤lim.word)
    (hstrideWord : (stride : ℤ)≤lim.word) (htailWord : (tail : ℤ)≤lim.word)
    (hmulWord : (group : ℤ)*(stride : ℤ)≤lim.word)
    (hfWord : (fbase : ℤ)+(group : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word)
    (hgWord : (gbase : ℤ)+(group : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word)
    (hhWord : (hbase : ℤ)+(group : ℤ)*(stride : ℤ)≤lim.word)
    (hD : LightTernaryPreparedWanted.D Q f.T=LightTernaryPreparedWanted.D Qstar f.T)
    (hvalue : |value|≤lim.word) (hd : d<lim.depth)
    (hquery : Meets lim P pPrepare (d+1)
      (LightTernaryPreparedWanted.args out (hbase+group*stride) caps
        (sourceConfig f fbase stride tail group) (sourceConfig g gbase stride tail group) Q)
      μ t (fun v ν => v=value ∧ Kept μ ν f.a)) :
    Meets lim P pMain d (args f g Qstar out bankValues caps record dst fbase gbase hbase stride tail)
      μ (time t) (fun _ ν => ∃ μ', Kept μ μ' f.a ∧ ν=Function.update μ' dst value) := by sorry
