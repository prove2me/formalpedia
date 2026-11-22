-- Prove2me | Theorems.Thm_SZ_eventually_composite_sqrtTen
-- name    : SZ.eventually_composite_sqrtTen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:46.435314+00:00
-- url     : https://prove2.me/theorems/af92d446-d019-4bc4-b6be-915f3228096c
-- title:
--   SZ: eventually composite sqrt Ten
-- statement:
--   The composite corollary at `3 + √10`: all but finitely many `⌊ξ (3+√10)ⁿ⌋` are
--   composite, being divisible by `6`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L141-L146
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L141-L146

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.eventually_composite_sqrtTen :
    ∀ᶠ n in atTop,
      ¬ Prime ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ ∧
      1 < ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ := by sorry
