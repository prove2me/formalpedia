-- Prove2me | Theorems.Thm_SZ_isDigits_digitB
-- name    : SZ.isDigits_digitB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:33.546902+00:00
-- url     : https://prove2.me/theorems/21bfb089-4140-4ebf-9076-3cdd2e385226
-- title:
--   SZ: is Digits digit B
-- statement:
--   The SZ construction uses the is Digits digit B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L464-L467
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L464-L467

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

theorem SZ.isDigits_digitB : IsDigits 3 digitB := by sorry
