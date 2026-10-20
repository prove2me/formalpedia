-- Prove2me | Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_cell_is_fundamental_region
-- name    : SchwartzMap.PoissonSummation.Standard.half_open_cell_is_fundamental_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/b8e8083c-3420-475b-b2e6-256cd97b2745
-- title:
--   SchwartzMap.PoissonSummation.Standard.half_open_cell_is_fundamental_region
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

theorem SchwartzMap.PoissonSummation.Standard.half_open_cell_is_fundamental_region :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.referenceIntegerLattice d)
      (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by sorry
