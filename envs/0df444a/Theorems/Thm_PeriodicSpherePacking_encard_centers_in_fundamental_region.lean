-- Prove2me | Theorems.Thm_PeriodicSpherePacking_encard_centers_in_fundamental_region
-- name    : PeriodicSpherePacking.encard_centers_in_fundamental_region
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/203b031b-21ac-4a23-8dd8-6f9e7083b679
-- title:
--   PeriodicSpherePacking.encard_centers_in_fundamental_region
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
open Finset Set
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

theorem PeriodicSpherePacking.encard_centers_in_fundamental_region
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.centerOrbitCardinality := by sorry
