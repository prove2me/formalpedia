-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLiteralOutputCap_literal_output_lower_fiber_bound
-- name    : ThreeSum.WeightedGlobalLiteralOutputCap.literal_output_lower_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:36.299885+00:00
-- url     : https://prove2.me/theorems/9e19c68c-6a82-467d-94c1-0e8546ecdcb9
-- title:
--   Weighted Global Literal Output Cap: literal output lower fiber bound
-- statement:
--   The Weighted Global Literal Output Cap construction uses the literal output lower fiber bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L20-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L20-L51

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLiteralOutputCap
open Finset TernaryJointType TernaryCoverLocal TernaryCoverFibers WeightedGlobalPartitionCount
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
  [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

theorem ThreeSum.WeightedGlobalLiteralOutputCap.literal_output_lower_fiber_bound (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, G ≤ (univ.filter fun e => output e = q).card)
    (hadd : ∀ e : E, left e+right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G*outputFiberCount outputHash o ≤ Fintype.card K*τ := by sorry
