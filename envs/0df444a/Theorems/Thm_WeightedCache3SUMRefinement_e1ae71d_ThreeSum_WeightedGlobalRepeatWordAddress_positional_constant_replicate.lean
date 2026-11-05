-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRepeatWordAddress_positional_constant_replicate
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress.positional_constant_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:41:33.6541+00:00
-- url     : https://prove2.me/theorems/e63076a3-dc66-4ab1-859c-2ea664d9ee46
-- title:
--   positional_constant_replicate
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L23-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L23-L28

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatWordAddress
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress
open ThreeSum.LightTernaryRepeatWord
open TernaryJointType
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress.positional_constant_replicate {A : Type*} (x : A) (q b : ℤ) (r : ℕ) :
    Radix.positionalHash b (fun _ : A=>q) (List.replicate r x)=
      Radix.positionalHash b (fun y : ℤ=>y) (List.replicate r q) := by sorry
