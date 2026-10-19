-- Prove2me | Theorems.Thm_PeriodicConstantApprox_axis_lattice_covolume_eq_cell_volume
-- name    : PeriodicConstantApprox.axis_lattice_covolume_eq_cell_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/0efbf900-4220-4e96-92e5-1b4a8700306d
-- title:
--   PeriodicConstantApprox.axis_lattice_covolume_eq_cell_volume
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Filter
variable {d : ℕ}
open scoped ENNReal
open ZSpan

theorem PeriodicConstantApprox.axis_lattice_covolume_eq_cell_volume (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (axisCellLattice (d := d) L hL) volume =
      (volume (axisAlignedCell (d := d) L)).toReal := by sorry
