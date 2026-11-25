-- Prove2me | Theorems.Thm_SZ_Slice_bsel_dvd
-- name    : SZ.Slice.bsel_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:48:39.390654+00:00
-- url     : https://prove2.me/theorems/fce0a41b-d2d0-4861-aa02-09cac74ba1ca
-- title:
--   Slice: bsel dvd
-- statement:
--   The Slice construction uses the bsel dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L222-L226
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L222-L226

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

theorem SZ.Slice.bsel_dvd (w : ℝ) : S.p ∣ S.bsel w := by sorry
