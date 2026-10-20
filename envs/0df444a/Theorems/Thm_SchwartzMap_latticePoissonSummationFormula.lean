-- Prove2me | Theorems.Thm_SchwartzMap_latticePoissonSummationFormula
-- name    : SchwartzMap.latticePoissonSummationFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/d7ba5740-9c24-4146-b51b-ec91b689e6f9
-- title:
--   SchwartzMap.latticePoissonSummationFormula
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
open SchwartzMap
omit [Fact (0 < d)]

theorem SchwartzMap.latticePoissonSummationFormula (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
  ∑' m : polarIntegerLattice (d := d) Λ, (𝓕 ⇑f m) *
    Complex.exp (2 * Real.pi * Complex.I * ⟪v, m⟫_[ℝ]) := by sorry
