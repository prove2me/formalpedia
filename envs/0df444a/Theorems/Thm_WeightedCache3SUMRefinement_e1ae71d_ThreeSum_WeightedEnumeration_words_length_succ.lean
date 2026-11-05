-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_words_length_succ
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.words_length_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:16.653354+00:00
-- url     : https://prove2.me/theorems/8dbb7abb-e25e-46ce-ad30-db01e6855c9d
-- title:
--   words_length_succ
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Enumeration.lean#L100-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Enumeration.lean#L100-L103

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.words_length_succ (n t : ℕ) :
    (words (n + 1) t).length =
      ((digits t).map fun d => (words n (t - digitCost d)).length).sum := by sorry
