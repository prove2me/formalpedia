-- Prove2me | Theorems.Thm_SpherePacking_CohnElkies_real_lattice_sum_bounded_by_origin_term
-- name    : SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/f023fd33-9125-4768-94ea-353ee65215f6
-- title:
--   SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators SchwartzMap
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}

theorem SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by sorry
