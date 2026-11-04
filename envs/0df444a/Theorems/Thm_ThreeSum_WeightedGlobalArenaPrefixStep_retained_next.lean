-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixStep_retained_next
-- name    : ThreeSum.WeightedGlobalArenaPrefixStep.retained_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:29:28.873936+00:00
-- url     : https://prove2.me/theorems/46dfe009-3b8e-438c-a6ca-735f81d424ad
-- title:
--   Weighted Global Arena Prefix Step: retained next
-- statement:
--   The checked physical score of the next prefix is bounded using the
--   literal parent physical records. No assumed source/potential correspondence
--   remains: the bijections retain every actual ordinal and dictionary index.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L43-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixStep.lean#L43-L50

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

theorem ThreeSum.WeightedGlobalArenaPrefixStep.retained_next (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (r K : ℕ)
    (hrow : row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    value maps τ cap I L R row root Q (r+1) K≤
      nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
        (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by sorry
