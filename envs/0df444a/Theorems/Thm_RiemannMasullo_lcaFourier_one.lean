-- Prove2me | Theorems.Thm_RiemannMasullo_lcaFourier_one
-- name    : RiemannMasullo.lcaFourier_one
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:54:25.6532+00:00
-- url     : https://prove2.me/theorems/055fed19-bf66-4de2-9f25-86136f9362f2
-- title:
--   Fourier transform at the trivial character
-- statement:
--   Evaluation of the Fourier transform at the trivial character gives the integral of the function.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L71-L72

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

namespace RiemannMasullo

theorem lcaFourier_one (f : G → ℂ) (hf : Integrable f μ) :
    lcaFourier μ f 1 = ∫ x, f x ∂μ := by sorry

end RiemannMasullo
