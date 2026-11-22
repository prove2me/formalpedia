-- Prove2me | Theorems.Thm_SZ_three_dvd_floor_sqrtTen
-- name    : SZ.three_dvd_floor_sqrtTen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:29.282793+00:00
-- url     : https://prove2.me/theorems/5210d6a5-0d80-4d56-a752-73f522d5b4a6
-- title:
--   SZ: three dvd floor sqrt Ten
-- statement:
--   The SZ construction uses the three dvd floor sqrt Ten property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L131-L133
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L131-L133

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.three_dvd_floor_sqrtTen (n : ℕ) :
    (3 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ := by sorry
