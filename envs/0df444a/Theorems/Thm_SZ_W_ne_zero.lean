-- Prove2me | Theorems.Thm_SZ_W_ne_zero
-- name    : SZ.W_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:27.966727+00:00
-- url     : https://prove2.me/theorems/93beabbc-9363-5a4e-be74-ccefef4c05fb
-- title:
--   SZ: W ne zero
-- statement:
--   The SZ construction uses the W ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L271-L273
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L271-L273

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

theorem SZ.W_ne_zero (k : ℕ) : W k ≠ 0 := by sorry
