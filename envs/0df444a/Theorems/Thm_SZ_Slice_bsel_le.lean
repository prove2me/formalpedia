-- Prove2me | Theorems.Thm_SZ_Slice_bsel_le
-- name    : SZ.Slice.bsel_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:28.228163+00:00
-- url     : https://prove2.me/theorems/f23dad47-54d3-4ed2-ac2d-743bee9b7a8f
-- title:
--   Slice: bsel le
-- statement:
--   The Slice construction uses the bsel le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L220-L220
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L220-L220

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

theorem SZ.Slice.bsel_le (w : ℝ) : S.bsel w ≤ S.e := by sorry
