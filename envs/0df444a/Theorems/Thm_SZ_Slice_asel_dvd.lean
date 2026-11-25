-- Prove2me | Theorems.Thm_SZ_Slice_asel_dvd
-- name    : SZ.Slice.asel_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:48:47.477156+00:00
-- url     : https://prove2.me/theorems/f93f8cd0-28a3-47b0-8516-30e4dc2df799
-- title:
--   Slice: asel dvd
-- statement:
--   The Slice construction uses the asel dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L228-L228
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L228-L228

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

theorem SZ.Slice.asel_dvd (w : ℝ) : S.p ∣ S.asel w := by sorry
