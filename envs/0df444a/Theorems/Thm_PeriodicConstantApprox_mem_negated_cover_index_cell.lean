-- Prove2me | Theorems.Thm_PeriodicConstantApprox_mem_negated_cover_index_cell
-- name    : PeriodicConstantApprox.mem_negated_cover_index_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/72698545-b9d5-42b0-9ec6-53a92f5dbf2f
-- title:
--   PeriodicConstantApprox.mem_negated_cover_index_cell
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
open Metric
variable (L : ℝ) (hL : 0 < L)

theorem PeriodicConstantApprox.mem_negated_cover_index_cell (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ (-axisCellCoverIndex (d := d) L hL x) +ᵥ axisAlignedCell (d := d) L := by sorry
