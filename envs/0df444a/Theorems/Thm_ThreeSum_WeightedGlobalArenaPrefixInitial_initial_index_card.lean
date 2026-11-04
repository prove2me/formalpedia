-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInitial_initial_index_card
-- name    : ThreeSum.WeightedGlobalArenaPrefixInitial.initial_index_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:24:35.676702+00:00
-- url     : https://prove2.me/theorems/5b577c33-1c0c-432e-9f58-c3cb0cd9a475
-- title:
--   Weighted Global Arena Prefix Initial: initial index card
-- statement:
--   The Weighted Global Arena Prefix Initial construction uses the initial index card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L24-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L24-L46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
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

theorem ThreeSum.WeightedGlobalArenaPrefixInitial.initial_index_card (K : ℕ) :
    Fintype.card ((M maps τ cap I L R row root).Index 0 K)≤I.requesterCount*(I.nB*I.nC)^K := by sorry
