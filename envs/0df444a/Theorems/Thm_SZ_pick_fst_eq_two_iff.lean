-- Prove2me | Theorems.Thm_SZ_pick_fst_eq_two_iff
-- name    : SZ.pick_fst_eq_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:18.125836+00:00
-- url     : https://prove2.me/theorems/9f9824ea-1c85-460e-ae57-fa2f5735ad70
-- title:
--   SZ: pick fst eq two iff
-- statement:
--   `a = 2` is chosen exactly on the trap set `A = (U, 2√3) ∪ (2√3+U, 3U]`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L167-L177
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L167-L177

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

theorem SZ.pick_fst_eq_two_iff (w : ℝ) :
    (pick w).1 = 2 ↔ ((1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w) := by sorry
