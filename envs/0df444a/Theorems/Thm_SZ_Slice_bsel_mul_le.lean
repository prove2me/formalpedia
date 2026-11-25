-- Prove2me | Theorems.Thm_SZ_Slice_bsel_mul_le
-- name    : SZ.Slice.bsel_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:49:37.363729+00:00
-- url     : https://prove2.me/theorems/5c2824a2-5da8-52fd-ac2c-334aee29a0f8
-- title:
--   Slice: bsel mul le
-- statement:
--   The Slice construction uses the bsel mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L235-L248
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L235-L248

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

theorem SZ.Slice.bsel_mul_le (w : ℝ) : (S.bsel w : ℝ) * S.sq ≤ w := by sorry
