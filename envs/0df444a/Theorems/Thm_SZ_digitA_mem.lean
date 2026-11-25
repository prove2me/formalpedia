-- Prove2me | Theorems.Thm_SZ_digitA_mem
-- name    : SZ.digitA_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:00.94026+00:00
-- url     : https://prove2.me/theorems/72f4c218-52f6-40e2-80ba-504deb608d58
-- title:
--   SZ: digit A mem
-- statement:
--   The SZ construction uses the digit A mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L224-L224
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L224-L224

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

theorem SZ.digitA_mem (k : ℕ) : digitA k = 0 ∨ digitA k = 2 := by sorry
