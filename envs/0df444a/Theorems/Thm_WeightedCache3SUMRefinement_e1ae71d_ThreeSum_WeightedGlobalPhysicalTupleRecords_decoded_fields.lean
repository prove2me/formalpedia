-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalTupleRecords_decoded_fields
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:47:56.946124+00:00
-- url     : https://prove2.me/theorems/9a495580-0248-4320-9c89-a96c98d55030
-- title:
--   decoded_fields
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L54-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L54-L64

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields (base : List A) (r M n p R F : ℕ) (input : ℕ→ℤ)
    (raw word group : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    dictionary (base.map word) R r x.val.2=
      Radix.positionalHash (R : ℤ) word (decodeRecord base r M n p input raw x).2.val ∧
    dictionary (base.map group) F r x.val.2=
      Radix.positionalHash (F : ℤ) group (decodeRecord base r M n p input raw x).2.val := by sorry
