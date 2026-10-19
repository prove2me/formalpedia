-- Prove2me | Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_character_translate_integrable_on_cell
-- name    : SchwartzMap.PoissonSummation.Standard.fourier_character_translate_integrable_on_cell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/53a16560-1d07-4e5c-a6f1-63d07141100a
-- title:
--   SchwartzMap.PoissonSummation.Standard.fourier_character_translate_integrable_on_cell
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

theorem SchwartzMap.PoissonSummation.Standard.fourier_character_translate_integrable_on_cell (n : Fin d → ℤ)
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) :
    IntegrableOn
        (fun x : (EuclideanSpace ℝ (Fin d)) =>
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d)))))
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by sorry
