-- Prove2me | Theorems.Thm_RiemannMasullo_pointMassRepresentative_fourier_zero
-- name    : RiemannMasullo.pointMassRepresentative_fourier_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:56:20.742645+00:00
-- url     : https://prove2.me/theorems/64f4d9b0-63dc-4822-9b2c-2f0287c9aee3
-- title:
--   A nonzero representative with identically zero Fourier transform
-- statement:
--   The function on the real line which is one at zero and zero elsewhere is integrable and has identically zero Fourier transform, although its value at zero is one. Thus the transform cannot recover every point value of an arbitrary integrable representative.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L135-L137

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set

noncomputable local instance : MeasurableSpace (Multiplicative ℝ) := (inferInstance : MeasurableSpace ℝ)

namespace RiemannMasullo
theorem pointMassRepresentative_fourier_zero (f : ℝ → ℂ) (hf : f = Set.indicator ({0} : Set ℝ) (fun _ ↦ (1 : ℂ))) :
    f 0 = 1 ∧ Integrable f volume ∧
      ∀ χ : PontryaginDual (Multiplicative ℝ),
        lcaFourier (G := Multiplicative ℝ) (show Measure (Multiplicative ℝ) from (volume : Measure ℝ))
          (fun x ↦ f x.toAdd) χ = 0 := by sorry
end RiemannMasullo
