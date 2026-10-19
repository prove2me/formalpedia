-- Prove2me | Theorems.Thm_SchwartzMap_PoissonSummation_Standard_summable_cell_integrals_of_weighted_translates
-- name    : SchwartzMap.PoissonSummation.Standard.summable_cell_integrals_of_weighted_translates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/1437791d-d23a-4be6-868f-c740610d97fd
-- title:
--   SchwartzMap.PoissonSummation.Standard.summable_cell_integrals_of_weighted_translates
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

theorem SchwartzMap.PoissonSummation.Standard.summable_cell_integrals_of_weighted_translates (n : Fin d → ℤ) :
    Summable
        (fun ℓ : (SchwartzMap.referenceIntegerLattice d) =>
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
                f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) := by sorry
