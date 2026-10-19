-- Prove2me | Theorems.Thm_SchwartzMap_UnitAddTorus_fourier_character_coordinate_projection_ofLp
-- name    : SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection_ofLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/7158a2db-9b0d-4720-8b9e-92598cbea91b
-- title:
--   SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection_ofLp
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus

theorem SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by sorry
