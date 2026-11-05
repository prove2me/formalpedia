-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:38:03.919237+00:00
-- url     : https://prove2.me/theorems/f1aead7b-92a2-4e7a-be61-9962da2a2597
-- title:
--   equiv_val
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L51-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTupleDictionaryDecode.lean#L51-L52

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ)
    (j : Fin (base.length^r)) : (equiv base hn r j).val=decode base r j := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
