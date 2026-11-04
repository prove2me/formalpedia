-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_key_collisions
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.key_collisions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:21.820203+00:00
-- url     : https://prove2.me/theorems/26a4f628-2196-4d5a-8391-39097848a30d
-- title:
--   Weighted Global Arena Selected Signed: key collisions
-- statement:
--   No multiplicity is lost when packed keys replace original row vectors.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L124-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L124-L132

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.key_collisions (A : Inputs) (s : State (p := p) A) (r q : ℕ) (L : ℕ→ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (hashMap A s r (fun t => (L i.val t.val : ZMod p))))).card=
      collisions A s.row L r q := by sorry
