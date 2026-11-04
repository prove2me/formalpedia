-- Prove2me | Theorems.Thm_WeightedCache_cost_add_deficit
-- name    : WeightedCache.cost_add_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:24.736092+00:00
-- url     : https://prove2.me/theorems/37fdf5ce-91d1-4e3f-bde1-0deb00f7867e
-- title:
--   Weighted Cache: cost add deficit
-- statement:
--   The Weighted Cache construction uses the cost add deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L55-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L55-L61

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
import Definitions.Def_Submission_Weighted_Cache
set_option autoImplicit false
open WeightedCache
open Finset

theorem WeightedCache.cost_add_deficit {N : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) : cost c R + deficit c Q R = cost c Q := by sorry
