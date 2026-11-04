-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInitial_actual_initializer_bound
-- name    : ThreeSum.WeightedGlobalArenaPrefixInitial.actual_initializer_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:26:05.494501+00:00
-- url     : https://prove2.me/theorems/54234084-2e67-4608-86bc-6d992599f720
-- title:
--   Weighted Global Arena Prefix Initial: actual initializer bound
-- statement:
--   The Weighted Global Arena Prefix Initial construction uses the actual initializer bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L70-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInitial.lean#L70-L82

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

theorem ThreeSum.WeightedGlobalArenaPrefixInitial.actual_initializer_bound (K b n : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hB : I.nB≤n) (hC : I.nC≤n) :
    value maps τ cap I L R row root Q 0 K≤
      I.requesterCount*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by sorry
