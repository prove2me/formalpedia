-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_good_of_seed
-- name    : ThreeSum.WeightedGlobalArenaFamilyBudget.good_of_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:32:53.522758+00:00
-- url     : https://prove2.me/theorems/70902387-e1b5-4e33-9436-874eb674bbea
-- title:
--   Weighted Global Arena Family Budget: good of seed
-- statement:
--   The existential average witness is an actual integer ordinal visited by
--   Controller166, with the literal admissibility flag and actual three scores.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L72-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L72-L96

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

theorem ThreeSum.WeightedGlobalArenaFamilyBudget.good_of_seed (n U0 : ℕ) (seed : E×E)
    (hs : seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows))
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hp : (p^(2*K))^(r+1)*(scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K seed)≤
      scale m r K*(9*pairFactor m F K)^(r+1)*U0)
    (hb : p^(r+1)*nextCollision A ℓ row L r I.nB seed≤9^(r+1)*n^2)
    (hc : p^(r+1)*nextCollision A ℓ row R r I.nC seed≤9^(r+1)*n^2) :
    ∃i<N, LightTernaryRowSelector.Good
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).flag
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreB
      (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreC
      ((D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog).scoreP K)
      (p^(r+1)) (p^(r+1)) ((p^(2*K))^(r+1))
      (9^(r+1)*n^2) (9^(r+1)*n^2) (scale m r K*(9*pairFactor m F K)^(r+1)*U0) i := by sorry
