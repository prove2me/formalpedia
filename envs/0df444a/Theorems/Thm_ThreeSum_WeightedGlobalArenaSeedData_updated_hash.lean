-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_updated_hash
-- name    : ThreeSum.WeightedGlobalArenaSeedData.updated_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:15:22.123956+00:00
-- url     : https://prove2.me/theorems/dec5b795-5dbe-4e39-a941-b8811dcd6a84
-- title:
--   Weighted Global Arena Seed Data: updated hash
-- statement:
--   The Weighted Global Arena Seed Data construction uses the updated hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L52-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L52-L60

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedData
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaSeedData.updated_hash {J r : ℕ}
    (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (newrow : (Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (v : ℕ→Fin (J+2)→ℤ) (i : ℕ) :
    hash (Function.update row r newrow) (r+1) v i=
      appendVector (hash row r v i) (newrow (fun t => (v i t : ZMod p))) := by sorry
