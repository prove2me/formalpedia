-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixStep_next_eq_physical
-- name    : ThreeSum.WeightedGlobalArenaPrefixStep.next_eq_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:29:27.069212+00:00
-- url     : https://prove2.me/theorems/e88bae61-eeab-40fb-bc48-91b0037b7850
-- title:
--   Weighted Global Arena Prefix Step: next eq physical
-- statement:
--   The Weighted Global Arena Prefix Step construction uses the next eq physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L26-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L26-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPrefixStep.next_eq_physical (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (r K : ℕ) :
    nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
      ((M maps τ cap I L R row root).matrix (r := r) (K := K)) maps seed=
    nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
      (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by sorry
