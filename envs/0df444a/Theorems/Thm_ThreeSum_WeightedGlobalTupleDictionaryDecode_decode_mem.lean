-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_mem
-- name    : ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:44.86885+00:00
-- url     : https://prove2.me/theorems/71416c1b-63aa-41aa-abb1-dec394265a99
-- title:
--   Weighted Global Tuple Dictionary Decode: decode mem
-- statement:
--   The Weighted Global Tuple Dictionary Decode construction uses the decode mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L19-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L19-L20

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_mem {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    decode base r j∈RadixKeyLists.tuples base r := by sorry
