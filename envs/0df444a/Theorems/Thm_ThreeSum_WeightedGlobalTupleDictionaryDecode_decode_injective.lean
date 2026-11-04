-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_injective
-- name    : ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:52:40.138792+00:00
-- url     : https://prove2.me/theorems/e7b74bb8-5338-4c33-911d-f0c260a9fe54
-- title:
--   Weighted Global Tuple Dictionary Decode: decode injective
-- statement:
--   Distinct source dictionary positions remain distinct after decoding,
--   including native hash collisions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L37-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L37-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_injective {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ) :
    Function.Injective (decode base r) := by sorry
