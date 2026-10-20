-- Prove2me | Theorems.Thm_SpherePacking_CohnElkies_origin_character_sum_norm_sq_eq_orbit_count_sq
-- name    : SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/bfddc2a8-413b-42c1-af1e-4150bdf999de
-- title:
--   SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies

theorem SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * Complex.I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2
      =
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 := by sorry
