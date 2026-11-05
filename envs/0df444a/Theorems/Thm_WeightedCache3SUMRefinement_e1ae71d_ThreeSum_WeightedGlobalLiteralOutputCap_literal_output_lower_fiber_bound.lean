-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLiteralOutputCap_literal_output_lower_fiber_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLiteralOutputCap.literal_output_lower_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:21:31.632407+00:00
-- url     : https://prove2.me/theorems/c926c0f4-7ba2-486e-8965-2d74da62d363
-- title:
--   literal_output_lower_fiber_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L20-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L20-L51

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
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
  [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLiteralOutputCap.literal_output_lower_fiber_bound (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, G ≤ (univ.filter fun e => output e = q).card)
    (hadd : ∀ e : E, left e+right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G*outputFiberCount outputHash o ≤ Fintype.card K*τ := by sorry
