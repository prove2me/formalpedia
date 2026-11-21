-- Prove2me | Theorems.Thm_RiemannMasullo_lcaConvolution_subsingleton
-- name    : RiemannMasullo.lcaConvolution_subsingleton
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:54:26.869236+00:00
-- url     : https://prove2.me/theorems/8304b2da-518a-4b53-92b6-f993f69281ee
-- title:
--   Convolution on a one-point group
-- statement:
--   On a one-point group convolution equals the product of the function values multiplied by the total measure.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L81-L82

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
open RiemannMasullo MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

namespace RiemannMasullo

theorem lcaConvolution_subsingleton [Subsingleton G] (f g : G → ℂ) (x : G) :
    lcaConvolution μ f g x = (μ univ).toReal * f x * g x := by sorry

end RiemannMasullo
