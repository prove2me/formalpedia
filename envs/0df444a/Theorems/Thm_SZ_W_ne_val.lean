-- Prove2me | Theorems.Thm_SZ_W_ne_val
-- name    : SZ.W_ne_val
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:37.133972+00:00
-- url     : https://prove2.me/theorems/5b26f0b1-d181-4565-9f2e-2de651466f22
-- title:
--   SZ: W ne val
-- statement:
--   No state is ever a candidate trap fixed point: `W k = p + q√3` forces `q` to be the
--   state's `√3`-coordinate, which is `≥ 9`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L264-L269
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L264-L269

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

theorem SZ.W_ne_val (k : ℕ) {p q : ℤ} (hq : q < 9) :
    W k ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by sorry
