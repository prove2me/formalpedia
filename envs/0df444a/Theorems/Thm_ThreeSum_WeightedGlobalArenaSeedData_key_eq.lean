-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_key_eq
-- name    : ThreeSum.WeightedGlobalArenaSeedData.key_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:19:04.241327+00:00
-- url     : https://prove2.me/theorems/764c80e8-2b4e-4ef6-8c9e-c63810570bda
-- title:
--   Weighted Global Arena Seed Data: key eq
-- statement:
--   The Weighted Global Arena Seed Data construction uses the key eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L62-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L62-L74

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

theorem ThreeSum.WeightedGlobalArenaSeedData.key_eq (I : Input) (A : Inputs) (r b k : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (v : ℕ→Fin (A.J+2)→ℤ) (hv : ∀ i t, 0≤(p : ℤ)+v i t) (i : ℕ) :
    LightTernaryAppendKeys.key p (p^r) (A.J+2)
      (fun i => coefficientCode (hash row r v i)) (physical v)
      (fun k => if hk : k<A.J+2 then (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val else 0) i=
      coefficientCode (hash (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (r+1) v i) := by sorry
