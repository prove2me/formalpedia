-- Prove2me | Theorems.Thm_SZ_isDigits_digitA
-- name    : SZ.isDigits_digitA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:29.860513+00:00
-- url     : https://prove2.me/theorems/295b2763-1d0e-4522-b576-235fd3ca66b0
-- title:
--   SZ: is Digits digit A
-- statement:
--   The SZ construction uses the is Digits digit A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L459-L462
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L459-L462

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

theorem SZ.isDigits_digitA : IsDigits 3 digitA := by sorry
