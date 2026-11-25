-- Prove2me | Theorems.Thm_SZ_Slice_p_cast_ne
-- name    : SZ.Slice.p_cast_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:21.042011+00:00
-- url     : https://prove2.me/theorems/c15b3c8c-2429-410a-8de8-678f0dfebc24
-- title:
--   Slice: p cast ne
-- statement:
--   The Slice construction uses the p cast ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L146-L146
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L146-L146

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

theorem SZ.Slice.p_cast_ne : (S.p : ℝ) ≠ 0 := by sorry
