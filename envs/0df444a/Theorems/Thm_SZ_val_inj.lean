-- Prove2me | Theorems.Thm_SZ_val_inj
-- name    : SZ.val_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:23:54.867305+00:00
-- url     : https://prove2.me/theorems/61981330-c29c-4322-a8ec-1fd337a396a0
-- title:
--   SZ: val inj
-- statement:
--   `ℤ[√3]` is free on `1, √3`: the coordinates of a state are well defined.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L100-L111
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L100-L111

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

theorem SZ.val_inj {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 3 = (p' : ℝ) + (q' : ℝ) * Real.sqrt 3) :
    p = p' ∧ q = q' := by sorry
