-- Prove2me | Theorems.Thm_PeriodicSpherePacking_orbit_cardinality_eq_bounded_representatives
-- name    : PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/66b798de-6159-421f-8959-14b8ac5915d6
-- title:
--   PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives
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
variable {d : ℕ}

theorem PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
  S.centerOrbitCardinality = S.boundedCenterRepresentativeCount hd hD_isBounded := by sorry
