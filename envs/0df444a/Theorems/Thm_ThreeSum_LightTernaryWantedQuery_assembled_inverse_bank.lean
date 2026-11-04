-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedQuery_assembled_inverse_bank
-- name    : ThreeSum.LightTernaryWantedQuery.assembled_inverse_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:47.623312+00:00
-- url     : https://prove2.me/theorems/f0f934f6-ed11-4ff4-957d-c41070d92352
-- title:
--   Light Ternary Wanted Query: assembled inverse bank
-- statement:
--   The Light Ternary Wanted Query construction uses the assembled inverse bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L130-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L130-L135

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedQuery.assembled_inverse_bank {N T n base : ℕ} (E : Enumeration N T n)
    (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryBankAssembly.product F G)) base N μ) :
    LightTernaryBankSweep.Stages E (fun k => stageValue k (H F G)) base N μ := by sorry
