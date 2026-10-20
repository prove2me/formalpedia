-- Prove2me | Theorems.Thm_PeriodicConstant_inset_cell_eq_coordinate_preimage
-- name    : PeriodicConstant.inset_cell_eq_coordinate_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/aaf7aa4b-475a-428f-88c3-66bba4ce617f
-- title:
--   PeriodicConstant.inset_cell_eq_coordinate_preimage
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
open scoped Pointwise
open PeriodicConstant
variable {d : ℕ}

theorem PeriodicConstant.inset_cell_eq_coordinate_preimage (L r : ℝ) :
    insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by sorry
