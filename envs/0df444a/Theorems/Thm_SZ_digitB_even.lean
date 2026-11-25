-- Prove2me | Theorems.Thm_SZ_digitB_even
-- name    : SZ.digitB_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:36.032473+00:00
-- url     : https://prove2.me/theorems/60ff152f-be46-4ad9-a137-a07dc618c7ff
-- title:
--   SZ: digit B even
-- statement:
--   The SZ construction uses the digit B even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L231-L232
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L231-L232

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

theorem SZ.digitB_even (k : ℕ) : Even (digitB k) := by sorry
