-- Prove2me | Theorems.Thm_SZ_Slice_w0_def
-- name    : SZ.Slice.w0_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:01.892801+00:00
-- url     : https://prove2.me/theorems/8fe8e975-0c87-4805-abf9-c8f54fc7323b
-- title:
--   Slice: w0 def
-- statement:
--   The Slice construction uses the w0 def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L565-L565
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L565-L565

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
variable {S}

theorem SZ.Slice.w0_def (S : Slice) (j k₀ : ℤ) : S.w0 j k₀ = (S.m : ℝ) * S.sigma j k₀ := by sorry
