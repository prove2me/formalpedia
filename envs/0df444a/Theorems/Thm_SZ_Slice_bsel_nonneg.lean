-- Prove2me | Theorems.Thm_SZ_Slice_bsel_nonneg
-- name    : SZ.Slice.bsel_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:48:46.871155+00:00
-- url     : https://prove2.me/theorems/282ef0fa-2092-4393-8b05-a84b6305bca2
-- title:
--   Slice: bsel nonneg
-- statement:
--   The Slice construction uses the bsel nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L230-L233
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L230-L233

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

theorem SZ.Slice.bsel_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ S.bsel w := by sorry
