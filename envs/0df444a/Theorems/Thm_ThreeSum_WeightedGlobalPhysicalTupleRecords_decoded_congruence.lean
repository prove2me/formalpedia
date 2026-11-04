-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPhysicalTupleRecords_decoded_congruence
-- name    : ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:21:04.760929+00:00
-- url     : https://prove2.me/theorems/8985fe4d-9695-4253-abc0-bbf16aedaa37
-- title:
--   Weighted Global Physical Tuple Records: decoded congruence
-- statement:
--   The Weighted Global Physical Tuple Records construction uses the decoded congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L43-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPhysicalTupleRecords.lean#L43-L51

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

theorem ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    (M : ℤ)∣input x.val.1-Radix.positionalHash (p : ℤ) raw
      (decodeRecord base r M n p input raw x).2.val := by sorry
