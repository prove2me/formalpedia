-- Prove2me | Theorems.Thm_SZ_Slice_dB_eq
-- name    : SZ.Slice.dB_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:09.491801+00:00
-- url     : https://prove2.me/theorems/311647b6-44ec-404d-a25f-4c8a1d77d29a
-- title:
--   Slice: d B eq
-- statement:
--   The Slice construction uses the d B eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L418-L418
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L418-L418

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

theorem SZ.Slice.dB_eq (w₀ : ℝ) (k : ℕ) : S.dB w₀ k = S.bsel (S.W w₀ k) := by sorry
