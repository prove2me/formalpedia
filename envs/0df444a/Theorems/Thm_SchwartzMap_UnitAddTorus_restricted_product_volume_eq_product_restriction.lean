-- Prove2me | Theorems.Thm_SchwartzMap_UnitAddTorus_restricted_product_volume_eq_product_restriction
-- name    : SchwartzMap.UnitAddTorus.restricted_product_volume_eq_product_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.954123+00:00
-- url     : https://prove2.me/theorems/ca52773a-83a7-4723-9717-64d96ad2639f
-- title:
--   SchwartzMap.UnitAddTorus.restricted_product_volume_eq_product_restriction
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

theorem SchwartzMap.UnitAddTorus.restricted_product_volume_eq_product_restriction (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by sorry
