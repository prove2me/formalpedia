-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_flag_eq_one_iff
-- name    : ThreeSum.WeightedGlobalArenaSeedData.flag_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:16:55.875173+00:00
-- url     : https://prove2.me/theorems/87b6553f-85e9-4b18-b723-c78d5dd40f0c
-- title:
--   Weighted Global Arena Seed Data: flag eq one iff
-- statement:
--   The Weighted Global Arena Seed Data construction uses the flag eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L129-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L129-L139

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


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

theorem ThreeSum.WeightedGlobalArenaSeedData.flag_eq_one_iff (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ) :
    (data I A r b k ℓ seed row L R O rows catalog).flag=1 ↔
      seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows) := by sorry
