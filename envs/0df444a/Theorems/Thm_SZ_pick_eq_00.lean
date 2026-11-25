-- Prove2me | Theorems.Thm_SZ_pick_eq_00
-- name    : SZ.pick_eq_00
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:29.543413+00:00
-- url     : https://prove2.me/theorems/c8663990-1b58-446a-9bf8-b0354f761224
-- title:
--   SZ: pick eq 00
-- statement:
--   The SZ construction uses the pick eq 00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L135-L136
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L135-L136

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

theorem SZ.pick_eq_00 {w : ℝ} (h : w ≤ 1 + Real.sqrt 3) : pick w = (0, 0) := by sorry
