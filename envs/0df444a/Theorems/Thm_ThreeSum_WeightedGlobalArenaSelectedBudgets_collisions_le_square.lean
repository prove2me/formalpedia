-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_collisions_le_square
-- name    : ThreeSum.WeightedGlobalArenaSelectedBudgets.collisions_le_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:42:36.235584+00:00
-- url     : https://prove2.me/theorems/ccbc83e0-e23f-4043-95c2-d11f84f68239
-- title:
--   Weighted Global Arena Selected Budgets: collisions le square
-- statement:
--   The Weighted Global Arena Selected Budgets construction uses the collisions le square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L97-L103

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedBudgets
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)

theorem ThreeSum.WeightedGlobalArenaSelectedBudgets.collisions_le_square (j : ℕ) (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L : ℕ→ℕ→ℤ) (q : ℕ) : collisions A row L j q≤q^2 := by sorry
