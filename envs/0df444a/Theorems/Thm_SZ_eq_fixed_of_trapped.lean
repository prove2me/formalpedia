-- Prove2me | Theorems.Thm_SZ_eq_fixed_of_trapped
-- name    : SZ.eq_fixed_of_trapped
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:10.611812+00:00
-- url     : https://prove2.me/theorems/aa808a9c-0d98-4a04-9367-030af0d2e415
-- title:
--   SZ: eq fixed of trapped
-- statement:
--   If from step `K` on the orbit obeys one affine `3`-expanding map and stays bounded,
--   it sits at that map's fixed point `c/2`.  This is the whole dynamical input of L1.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L289-L307
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L289-L307

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

theorem SZ.eq_fixed_of_trapped {f : ℕ → ℝ} {c D : ℝ} {K : ℕ}
    (hrec : ∀ k, K ≤ k → f (k + 1) = 3 * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / 2| ≤ D) : f K = c / 2 := by sorry
