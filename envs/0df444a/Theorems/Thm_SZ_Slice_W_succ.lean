-- Prove2me | Theorems.Thm_SZ_Slice_W_succ
-- name    : SZ.Slice.W_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:57.714727+00:00
-- url     : https://prove2.me/theorems/5d29d2d2-5178-4442-a7a2-5f79a428a2d1
-- title:
--   Slice: W succ
-- statement:
--   The Slice construction uses the W succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L407-L408
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L407-L408

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)

theorem SZ.Slice.W_succ (w₀ : ℝ) (k : ℕ) :
    S.W w₀ (k + 1) = (S.m : ℝ) * (S.W w₀ k - S.val (S.pick (S.W w₀ k))) := by sorry
