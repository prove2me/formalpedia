-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_lineage_injective
-- name    : ThreeSum.WeightedGlobalNativePrefixLineage.Model.lineage_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:14:02.645957+00:00
-- url     : https://prove2.me/theorems/644218e1-f5bc-421d-a4f7-83914a3e3123
-- title:
--   Model: lineage injective
-- statement:
--   Original requester/carry IDs, original endpoint IDs, map occurrences,
--   outputs and every ordered local partition can all be reconstructed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L77-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L77-L107

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_Submission_Weighted_Global_TernaryNativePrefixLineage
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

theorem ThreeSum.WeightedGlobalNativePrefixLineage.Model.lineage_injective (r K : ℕ) : Function.Injective (M.lineage (r := r) (K := K)) := by sorry
