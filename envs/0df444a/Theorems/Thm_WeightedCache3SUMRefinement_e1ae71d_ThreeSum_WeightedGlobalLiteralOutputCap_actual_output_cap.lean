-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLiteralOutputCap_actual_output_cap
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:21:41.845207+00:00
-- url     : https://prove2.me/theorems/be0002c1-31f9-40b0-a545-f8bef0acf40c
-- title:
--   actual_output_cap
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L89-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L89-L104

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryLiteralOutputCap
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLiteralOutputCap
open Finset TernaryJointType TernaryCoverLocal TernaryCoverFibers WeightedGlobalPartitionCount
variable {p : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_cap (t r s τ : ℕ)
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (hraw : ∀ a b : ZMod p,
      rawPairCount (leftHash (α := alphaType t r s) (π := piType t r s) w) (rightHash w) a b ≤ τ)
    (o : ZMod p) :
    (2^(2*r)*3^(3*s))*outputFiberCount (actualOutputHash w) o ≤ partitionLoss r s*p*τ := by sorry
