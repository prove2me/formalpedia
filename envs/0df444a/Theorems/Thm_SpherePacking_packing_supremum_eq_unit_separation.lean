-- Prove2me | Theorems.Thm_SpherePacking_packing_supremum_eq_unit_separation
-- name    : SpherePacking.packing_supremum_eq_unit_separation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/c3721d69-bd6e-4ef7-827b-1eee7c4f0f15
-- title:
--   SpherePacking.packing_supremum_eq_unit_separation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking

theorem SpherePacking.packing_supremum_eq_unit_separation {d : ℕ} :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.upperPackingDensity := by sorry
