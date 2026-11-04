-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
-- name    : ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:51:29.608955+00:00
-- url     : https://prove2.me/theorems/ec330227-ce92-48ed-8f39-7847c75b0282
-- title:
--   Weighted Global Tuple Dictionary Decode: equiv val
-- statement:
--   The Weighted Global Tuple Dictionary Decode construction uses the equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L51-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L51-L52

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ)
    (j : Fin (base.length^r)) : (equiv base hn r j).val=decode base r j := by sorry

attribute [defeq] ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
