-- Prove2me | Theorems.Thm_SZ_Slice_le_asel
-- name    : SZ.Slice.le_asel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:48.262803+00:00
-- url     : https://prove2.me/theorems/a6a8551c-beab-580c-898f-b1dfd6324192
-- title:
--   Slice: le asel
-- statement:
--   The rule never overshoots: `v - U ≤ a`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L318-L330
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L318-L330

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

theorem SZ.Slice.le_asel (w : ℝ) : w - (S.bsel w : ℝ) * S.sq - S.U ≤ (S.asel w : ℝ) := by sorry
