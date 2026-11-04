-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalTupleRecords_decoded_fields
-- name    : ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:21:08.06499+00:00
-- url     : https://prove2.me/theorems/596ffca3-87ce-4046-b9b3-090ac2978b19
-- title:
--   Weighted Global Physical Tuple Records: decoded fields
-- statement:
--   Three separately allocated fields decode to the same physical tuple.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L54-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L54-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalTupleRecords
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}

theorem ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields (base : List A) (r M n p R F : ℕ) (input : ℕ→ℤ)
    (raw word group : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    dictionary (base.map word) R r x.val.2=
      Radix.positionalHash (R : ℤ) word (decodeRecord base r M n p input raw x).2.val ∧
    dictionary (base.map group) F r x.val.2=
      Radix.positionalHash (F : ℤ) group (decodeRecord base r M n p input raw x).2.val := by sorry
