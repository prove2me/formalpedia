-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_length
-- name    : ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:48.812271+00:00
-- url     : https://prove2.me/theorems/03e654da-c72c-4bd6-9b47-c8c390b6d00f
-- title:
--   Weighted Global Tuple Dictionary Decode: decode length
-- statement:
--   The Weighted Global Tuple Dictionary Decode construction uses the decode length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L22-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L22-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    (decode base r j).length=r := by sorry
