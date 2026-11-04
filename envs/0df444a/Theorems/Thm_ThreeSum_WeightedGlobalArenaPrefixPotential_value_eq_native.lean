-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_value_eq_native
-- name    : ThreeSum.WeightedGlobalArenaPrefixPotential.value_eq_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:28:20.672644+00:00
-- url     : https://prove2.me/theorems/7c4b2be1-66b3-4a33-90f9-965ca0f9c94b
-- title:
--   Weighted Global Arena Prefix Potential: value eq native
-- statement:
--   The Weighted Global Arena Prefix Potential construction uses the value eq native property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L53-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPotential.lean#L53-L66

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPairs
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPotential
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)

theorem ThreeSum.WeightedGlobalArenaPrefixPotential.value_eq_native {J : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input)
    (A B : ℕ→ℕ→ℤ) (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (root : ℕ→ℕ→ZMod p) (Q : WeightedGlobalGoodOutputCatalog.Output m) (r K : ℕ) :
    value maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q r K=
      WeightedGlobalNativeTensorScore.pairedPotential
        (S (r := r) maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q) K J A B := by sorry
