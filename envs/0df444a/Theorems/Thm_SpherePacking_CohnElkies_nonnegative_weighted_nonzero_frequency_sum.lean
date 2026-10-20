-- Prove2me | Theorems.Thm_SpherePacking_CohnElkies_nonnegative_weighted_nonzero_frequency_sum
-- name    : SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/d492bbc2-61a4-4af8-9b67-4a8abf7a9083
-- title:
--   SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum
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

theorem SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d)))
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) :
    0 ≤
      ∑' m : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice),
        (if m = (0 : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice)) then 0
        else
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              Complex.exp (2 * π * Complex.I *
                ⟪(x : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by sorry
