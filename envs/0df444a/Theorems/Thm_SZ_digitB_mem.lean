-- Prove2me | Theorems.Thm_SZ_digitB_mem
-- name    : SZ.digitB_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:00:06.443561+00:00
-- url     : https://prove2.me/theorems/d44051c9-7f47-446d-9107-d87423db3fd5
-- title:
--   SZ: digit B mem
-- statement:
--   The SZ construction uses the digit B mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L226-L226
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L226-L226

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

theorem SZ.digitB_mem (k : ℕ) : digitB k = 0 ∨ digitB k = 2 := by sorry
