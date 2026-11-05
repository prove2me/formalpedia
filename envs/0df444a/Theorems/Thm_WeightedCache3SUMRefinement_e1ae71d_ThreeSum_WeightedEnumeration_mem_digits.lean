-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:42.789748+00:00
-- url     : https://prove2.me/theorems/b1ee315e-f4cf-4130-a351-3c9e19e11dbd
-- title:
--   mem_digits
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Enumeration.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Enumeration.lean#L36-L37

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ digitCost d ≤ t := by sorry
