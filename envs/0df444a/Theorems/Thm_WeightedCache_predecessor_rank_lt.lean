-- Prove2me | Theorems.Thm_WeightedCache_predecessor_rank_lt
-- name    : WeightedCache.predecessor_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:56.357734+00:00
-- url     : https://prove2.me/theorems/3b971196-a538-46aa-864f-6741ded19df3
-- title:
--   Weighted Cache: predecessor rank lt
-- statement:
--   The Weighted Cache construction uses the predecessor rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L159-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L159-L171

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

theorem WeightedCache.predecessor_rank_lt {N : ℕ} (R : Word N) (i : Fin N)
    (hi : 0 < (R i).val) : rank (predecessor R i) < rank R := by sorry
