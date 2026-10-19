-- Prove2me | Theorems.Thm_SchwartzMap_lattice_covolume_eq_coordinate_determinant
-- name    : SchwartzMap.lattice_covolume_eq_coordinate_determinant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/b9536845-8804-4568-a681-4275886aa282
-- title:
--   SchwartzMap.lattice_covolume_eq_coordinate_determinant
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
open SchwartzMap
variable {d : ℕ}
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

theorem SchwartzMap.lattice_covolume_eq_coordinate_determinant :
    ZLattice.covolume L =
      abs ((LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ) ((latticeCoordinateEquiv L).toLinearMap)) := by sorry
