-- Prove2me | Theorems.Thm_SZ_pick_eq_20
-- name    : SZ.pick_eq_20
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:21.487371+00:00
-- url     : https://prove2.me/theorems/b9334613-f574-459e-ab55-6e521ddd2fd1
-- title:
--   SZ: pick eq 20
-- statement:
--   The SZ construction uses the pick eq 20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L138-L140
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L138-L140

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

theorem SZ.pick_eq_20 {w : ℝ} (h1 : 1 + Real.sqrt 3 < w) (h2 : w < 2 * Real.sqrt 3) :
    pick w = (2, 0) := by sorry
