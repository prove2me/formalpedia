-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_good_preserves
-- name    : ThreeSum.WeightedGlobalArenaFamilyBudget.good_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:29:47.774231+00:00
-- url     : https://prove2.me/theorems/01668ac1-df80-4b49-ab60-a1d13da981d9
-- title:
--   Weighted Global Arena Family Budget: good preserves
-- statement:
--   The actual chosen score test preserves all upper budgets. Positive
--   factorial scaling cancels; the initial paired potential is never evaluated.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L127-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L127-L150

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
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
open ThreeSum ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)

theorem ThreeSum.WeightedGlobalArenaFamilyBudget.good_preserves (n U0 i : ℕ)
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hg : budgetGood (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog) p m F r K n U0 i) :
    (p^(2*K))^(r+1)*nextValue maps τ cap I A ℓ row L R O Q r K (seedAt e i)≤
      (9*pairFactor m F K)^(r+1)*U0 ∧
      p^(r+1)*nextCollision A ℓ row L r I.nB (seedAt e i)≤9^(r+1)*n^2 ∧
      p^(r+1)*nextCollision A ℓ row R r I.nC (seedAt e i)≤9^(r+1)*n^2 := by sorry
