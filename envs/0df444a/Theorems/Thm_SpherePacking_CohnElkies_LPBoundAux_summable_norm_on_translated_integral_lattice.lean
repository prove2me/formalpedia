-- Prove2me | Theorems.Thm_SpherePacking_CohnElkies_LPBoundAux_summable_norm_on_translated_integral_lattice
-- name    : SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/42198bfc-1766-44d8-89b4-16f3cb320125
-- title:
--   SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped SchwartzMap
open scoped FourierTransform
open BigOperators
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
open SpherePacking.CohnElkies.LPBoundAux
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

theorem SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by sorry
