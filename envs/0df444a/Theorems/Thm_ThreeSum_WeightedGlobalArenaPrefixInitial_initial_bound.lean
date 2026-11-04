-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInitial_initial_bound
-- name    : ThreeSum.WeightedGlobalArenaPrefixInitial.initial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:24:43.79859+00:00
-- url     : https://prove2.me/theorems/8263efad-ab01-4e6b-affd-259011512638
-- title:
--   Weighted Global Arena Prefix Initial: initial bound
-- statement:
--   The Weighted Global Arena Prefix Initial construction uses the initial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L48-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L48-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_bound
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixInitial
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)

theorem ThreeSum.WeightedGlobalArenaPrefixInitial.initial_bound (K b : ℕ) (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b) :
    value maps τ cap I L R row root Q 0 K≤
      I.requesterCount*(I.nB*I.nC)^K*Λ^(K+K)*((K+K).factorial*b^(K+K))^2 := by sorry
