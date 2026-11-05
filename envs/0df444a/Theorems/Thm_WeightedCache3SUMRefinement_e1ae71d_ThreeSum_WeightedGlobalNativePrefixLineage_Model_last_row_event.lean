-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativePrefixLineage_Model_last_row_event
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model.last_row_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:29:18.767513+00:00
-- url     : https://prove2.me/theorems/b2134c6e-4185-4077-b060-7caa0454ffd7
-- title:
--   last_row_event
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L115-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L115-L131

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePrefixLineage
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model
variable (M : Model p Λ L F α π O B C)

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model.last_row_event {r K : ℕ} {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E]
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (hrow : M.row r=TernaryOriginalRowMenu.row Λ ℓ seed)
    (x : M.Index (r+1) K) :
    seed∈menuEvent ℓ (fun i j => (M.matrix (M.parent x) i j : ZMod p)) (childTarget M.maps (M.child x)) := by sorry
