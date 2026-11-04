-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePrefixLineage_Model_matrix_parent
-- name    : ThreeSum.WeightedGlobalNativePrefixLineage.Model.matrix_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:23:55.635997+00:00
-- url     : https://prove2.me/theorems/90bcc9d4-97fb-4c72-9f1f-73fb998fc14c
-- title:
--   Model: matrix parent
-- statement:
--   The Model construction uses the matrix parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L113-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePrefixLineage.lean#L113-L113

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

theorem ThreeSum.WeightedGlobalNativePrefixLineage.Model.matrix_parent {r K : ℕ} (x : M.Index (r+1) K) : M.matrix x=M.matrix (M.parent x) := by sorry
