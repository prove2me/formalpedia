-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:37:29.711344+00:00
-- url     : https://prove2.me/theorems/288560bc-2804-477e-a025-e5173cac41b2
-- title:
--   decode_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L22-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L22-L23

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    (decode base r j).length=r := by sorry
