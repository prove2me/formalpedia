-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_dictionary_decode
-- name    : ThreeSum.WeightedGlobalTupleDictionaryDecode.dictionary_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:46.314331+00:00
-- url     : https://prove2.me/theorems/52ae5fa6-618f-48aa-b329-466aa0170170
-- title:
--   Weighted Global Tuple Dictionary Decode: dictionary decode
-- statement:
--   The Weighted Global Tuple Dictionary Decode construction uses the dictionary decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L25-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L25-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem ThreeSum.WeightedGlobalTupleDictionaryDecode.dictionary_decode {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r))
    (raw : A→ℤ) (p : ℕ) :
    dictionary (base.map raw) p r j.val=Radix.positionalHash (p : ℤ) raw (decode base r j) := by sorry
