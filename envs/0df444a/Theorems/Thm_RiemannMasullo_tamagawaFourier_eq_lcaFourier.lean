-- Prove2me | Theorems.Thm_RiemannMasullo_tamagawaFourier_eq_lcaFourier
-- name    : RiemannMasullo.tamagawaFourier_eq_lcaFourier
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:55:58.023438+00:00
-- url     : https://prove2.me/theorems/8006021e-fa53-4c60-ba42-8c25d224d74c
-- title:
--   Identification of the Tamagawa and group Fourier integrals
-- statement:
--   If a character agrees with the additive character evaluated on products with a frequency, the two Fourier transforms agree at that frequency.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L204-L208

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]

local instance : MeasurableSpace (Multiplicative R) := ‹MeasurableSpace R›

namespace RiemannMasullo

theorem tamagawaFourier_eq_lcaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ)
    (y : R) (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ x : R, χ (Multiplicative.ofAdd x) = ψ (x * y)) :
    tamagawaFourier μ ψ f y = lcaFourier (G := Multiplicative R) μ
      (fun x ↦ f x.toAdd) χ := by sorry

end RiemannMasullo
