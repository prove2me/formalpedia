-- Prove2me | Theorems.Thm_PeriodicConstantApprox_axis_lattice_covolume_toNNReal
-- name    : PeriodicConstantApprox.axis_lattice_covolume_toNNReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/47e19254-8e3d-4650-92e6-bb84271a1a8f
-- title:
--   PeriodicConstantApprox.axis_lattice_covolume_toNNReal
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

theorem PeriodicConstantApprox.axis_lattice_covolume_toNNReal (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) =
      (volume (axisAlignedCell (d := d) L)).toNNReal := by sorry
