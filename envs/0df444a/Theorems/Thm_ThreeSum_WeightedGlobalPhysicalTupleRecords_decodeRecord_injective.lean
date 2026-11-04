-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalTupleRecords_decodeRecord_injective
-- name    : ThreeSum.WeightedGlobalPhysicalTupleRecords.decodeRecord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:20:12.621851+00:00
-- url     : https://prove2.me/theorems/ffbf19a2-e80e-49c7-90a4-b8cbb83dce1a
-- title:
--   Weighted Global Physical Tuple Records: decode Record injective
-- statement:
--   The Weighted Global Physical Tuple Records construction uses the decode Record injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L33-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L33-L41

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

theorem ThreeSum.WeightedGlobalPhysicalTupleRecords.decodeRecord_injective (base : List A) (hn : base.Nodup)
    (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :
    Function.Injective (decodeRecord base r M n p input raw) := by sorry
