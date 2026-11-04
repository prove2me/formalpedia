-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_retained_next_le
-- name    : ThreeSum.WeightedGlobalNativePrefixLineage.Model.retained_next_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:13:36.596026+00:00
-- url     : https://prove2.me/theorems/954e63a2-4acb-40c4-aeaf-8fae32d9c3d1
-- title:
--   Model: retained next le
-- statement:
--   The Model construction uses the retained next le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L133-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L133-L140

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_Submission_Weighted_Global_TernaryNativePrefixLineage
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
open ThreeSum.WeightedGlobalNativePrefixLineage.Model
variable (M : Model p Λ L F α π O B C)

theorem ThreeSum.WeightedGlobalNativePrefixLineage.Model.retained_next_le {r K : ℕ} {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E]
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (hrow : M.row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    potential (M.matrix (r := r+1) (K := K))≤
      nextPotential (α := α) (π := π) ℓ (M.matrix (r := r) (K := K)) M.maps seed := by sorry
