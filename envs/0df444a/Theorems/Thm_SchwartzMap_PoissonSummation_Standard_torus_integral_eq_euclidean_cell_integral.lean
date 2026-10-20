-- Prove2me | Theorems.Thm_SchwartzMap_PoissonSummation_Standard_torus_integral_eq_euclidean_cell_integral
-- name    : SchwartzMap.PoissonSummation.Standard.torus_integral_eq_euclidean_cell_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/d3ae953f-c770-456c-af7b-3cb1d24ed116
-- title:
--   SchwartzMap.PoissonSummation.Standard.torus_integral_eq_euclidean_cell_integral
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open MeasureTheory
open SchwartzMap
variable {d : ℕ}
open SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
open UnitAddTorus

theorem SchwartzMap.PoissonSummation.Standard.torus_integral_eq_euclidean_cell_integral (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (euclideanTorusProjection (d := d) x) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) := by sorry
