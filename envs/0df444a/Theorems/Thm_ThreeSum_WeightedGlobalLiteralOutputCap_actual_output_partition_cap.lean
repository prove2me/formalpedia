-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLiteralOutputCap_actual_output_partition_cap
-- name    : ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_partition_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:22.911455+00:00
-- url     : https://prove2.me/theorems/87cb967f-5205-49db-88a8-d2647bbf5910
-- title:
--   Weighted Global Literal Output Cap: actual output partition cap
-- statement:
--   Actual native output-hash fibers are paid by all original partitions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L68-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryLiteralOutputCap.lean#L68-L85

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

theorem ThreeSum.WeightedGlobalLiteralOutputCap.actual_output_partition_cap (t r s τ : ℕ)
    (w : TernaryCoverHashes.Coordinate (Fin (t+2*r+3*s)) → ZMod p)
    (hraw : ∀ a b : ZMod p,
      rawPairCount (leftHash (α := alphaType t r s) (π := piType t r s) w) (rightHash w) a b ≤ τ)
    (o : ZMod p) :
    partitionGroup r s*outputFiberCount (actualOutputHash w) o ≤ p*τ := by sorry
