-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_right_key_collisions
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.right_key_collisions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:51:10.997936+00:00
-- url     : https://prove2.me/theorems/ba73895b-c9cc-4c84-b2fd-db3a49171227
-- title:
--   Weighted Global Arena Selected Signed: right key collisions
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the right key collisions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L141-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L141-L146

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

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.right_key_collisions (A : Inputs) (s : State (p := p) A) (r q U radix : ℕ) (C : ℕ→ℤ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin q =>
      TernaryExtensionEncoding.coefficientCode (sourceRight (selectedHash A s r) U radix (C i.val)))).card=
      collisions A s.row (right U radix A.J C) r q := by sorry
