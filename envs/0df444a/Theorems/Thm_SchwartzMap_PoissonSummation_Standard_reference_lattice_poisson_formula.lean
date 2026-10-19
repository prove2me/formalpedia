-- Prove2me | Theorems.Thm_SchwartzMap_PoissonSummation_Standard_reference_lattice_poisson_formula
-- name    : SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/a37af0bd-7946-4ed8-880a-718437324f12
-- title:
--   SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

theorem SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula (v : (EuclideanSpace ℝ (Fin d))) :
    (∑' ℓ : (SchwartzMap.referenceIntegerLattice d), f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by sorry
