-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRowDispatch_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRowDispatch.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:00:45.629726+00:00
-- url     : https://prove2.me/theorems/ee131f80-80a9-4fd6-834b-1b84a960a9a6
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedRowDispatch.lean#L40-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedRowDispatch.lean#L40-L72

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedRowDispatch
import Theorems.Thm_Light_LocalsBut_update
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRowDispatch
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedRowDispatch.meets {pMain pPrepare N out bankValues caps record dst fbase gbase hbase stride tail group d t : ℕ}
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
    (hD : LightWeightedPreparedWanted.D Q f.T=LightWeightedPreparedWanted.D Qstar f.T)
    (hvalue : |value|≤lim.word) (hd : d<lim.depth)
    (hquery : Meets lim P pPrepare (d+1)
      (LightWeightedPreparedWanted.args out (hbase+group*stride) caps
        (sourceConfig f fbase stride tail group) (sourceConfig g gbase stride tail group) Q)
      μ t (fun v ν => v=value ∧ Kept μ ν f.a)) :
    Meets lim P pMain d (args f g Qstar out bankValues caps record dst fbase gbase hbase stride tail)
      μ (time t) (fun _ ν => ∃ μ', Kept μ μ' f.a ∧ ν=Function.update μ' dst value) := by sorry
