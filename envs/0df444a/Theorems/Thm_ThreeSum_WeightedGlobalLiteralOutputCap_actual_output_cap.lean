-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLiteralOutputCap_actual_output_cap
-- name    : ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:52.762526+00:00
-- url     : https://prove2.me/theorems/ebc76e92-2020-4072-8cbf-479c422b1e52
-- title:
--   Weighted Global Literal Output Cap: actual output cap
-- statement:
--   This recovers the full g-exponent output-volume estimate with only a
--   polynomial loss; no exact uniform-G assumption is required.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L89-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L89-L104

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLiteralOutputCap
open Finset TernaryJointType TernaryCoverLocal TernaryCoverFibers WeightedGlobalPartitionCount
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_cap (t r s τ : ℕ)
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (hraw : ∀ a b : ZMod p,
      rawPairCount (leftHash (α := alphaType t r s) (π := piType t r s) w) (rightHash w) a b ≤ τ)
    (o : ZMod p) :
    (2^(2*r)*3^(3*s))*outputFiberCount (actualOutputHash w) o ≤ partitionLoss r s*p*τ := by sorry
