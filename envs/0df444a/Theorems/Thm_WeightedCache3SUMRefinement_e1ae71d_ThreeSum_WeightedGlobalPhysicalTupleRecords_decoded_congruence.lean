-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalTupleRecords_decoded_congruence
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:47:58.769671+00:00
-- url     : https://prove2.me/theorems/0e3db085-f78c-47d0-bb0c-e5d08bb3b992
-- title:
--   decoded_congruence
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L43-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L43-L51

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    (M : ℤ)∣input x.val.1-Radix.positionalHash (p : ℤ) raw
      (decodeRecord base r M n p input raw x).2.val := by sorry
