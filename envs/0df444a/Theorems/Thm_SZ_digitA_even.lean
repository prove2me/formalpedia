-- Prove2me | Theorems.Thm_SZ_digitA_even
-- name    : SZ.digitA_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:08:45.232801+00:00
-- url     : https://prove2.me/theorems/e1991071-f16e-5634-94ee-7560b672a226
-- title:
--   SZ: digit A even
-- statement:
--   The SZ construction uses the digit A even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L228-L229
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L228-L229

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.digitA_even (k : ℕ) : Even (digitA k) := by sorry
