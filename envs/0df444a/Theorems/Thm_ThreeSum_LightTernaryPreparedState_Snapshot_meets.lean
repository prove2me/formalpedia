-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_meets
-- name    : ThreeSum.LightTernaryPreparedState.Snapshot.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:44:28.791141+00:00
-- url     : https://prove2.me/theorems/20083a2a-5ad7-44d2-b516-3e968136df37
-- title:
--   Snapshot: meets
-- statement:
--   The Snapshot construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedState.lean#L47-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedState.lean#L47-L58

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
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
open ThreeSum ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000

theorem ThreeSum.LightTernaryPreparedState.Snapshot.meets {lim : Limits} {P : Program} {e : LightTernaryPreparedWanted.Entries} {pMain N out bankValues caps d : ℕ}
    (hmain : P[pMain]?=some (LightTernaryPreparedWanted.body e)) (lib : LightTernaryPreparedWanted.Library P e)
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (hd : d+3*N+f.L+13≤lim.depth) :
    Meets lim P pMain d (LightTernaryPreparedWanted.args out bankValues caps f g Q) μ (LightTernaryPreparedWanted.time f g Q)
      (fun v ν => v=stageValue N (LightTernaryWantedQuery.H F G) Q ∧ Kept μ ν f.a) := by sorry
