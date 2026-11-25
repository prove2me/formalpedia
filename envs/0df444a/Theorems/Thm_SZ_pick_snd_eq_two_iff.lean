-- Prove2me | Theorems.Thm_SZ_pick_snd_eq_two_iff
-- name    : SZ.pick_snd_eq_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:11.793796+00:00
-- url     : https://prove2.me/theorems/bd6a4839-168f-4eb0-b98e-da3610ed0a19
-- title:
--   SZ: pick snd eq two iff
-- statement:
--   `b = 2` is chosen exactly when it is available: outside `L = [0, 2√3)`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L155-L164
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L155-L164

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

theorem SZ.pick_snd_eq_two_iff (w : ℝ) : (pick w).2 = 2 ↔ 2 * Real.sqrt 3 ≤ w := by sorry
