-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_root_update
-- name    : ThreeSum.WeightedGlobalArenaSeedData.root_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:19:34.943792+00:00
-- url     : https://prove2.me/theorems/b9e86846-6d04-4a47-a023-a8836baaf4a6
-- title:
--   Weighted Global Arena Seed Data: root update
-- statement:
--   The Weighted Global Arena Seed Data construction uses the root update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L104-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L104-L112

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

theorem ThreeSum.WeightedGlobalArenaSeedData.root_update {J : ℕ}
    (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (newrow : (Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p) (O : ℕ→Fin (J+2)→ℤ) (r : ℕ) :
    root (Function.update row r newrow) O=
      fun o => Function.update (root row O o) r (newrow (fun t => (O o t : ZMod p))) := by sorry
