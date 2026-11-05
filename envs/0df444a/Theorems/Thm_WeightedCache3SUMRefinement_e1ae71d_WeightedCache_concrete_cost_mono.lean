-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_concrete_cost_mono
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.concrete_cost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:48.782041+00:00
-- url     : https://prove2.me/theorems/3b9ad0de-72f4-4557-862d-6d0360099fdc
-- title:
--   concrete_cost_mono
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L255-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L255-L257

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.concrete_cost_mono : Monotone (![0, 1369, 2740] : Fin 3 → ℕ) := by sorry
