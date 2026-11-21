-- Prove2me | Theorems.Thm_RiemannMasullo_lcaCosetIntegral_mk
-- name    : RiemannMasullo.lcaCosetIntegral_mk
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:13:11.988162+00:00
-- url     : https://prove2.me/theorems/573b5a67-bf62-46cd-8f4d-fbb014b78618
-- title:
--   Independence of the representative in the coset integral
-- statement:
--   For a Haar measure on a subgroup and a function integrable on a coset, the coset integral can be evaluated using any representative of that coset.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L161-L164

import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _

namespace RiemannMasullo

theorem lcaCosetIntegral_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G)
    (hf : Integrable (fun h : H ↦ f (x * (h : G))) μH) :
    lcaCosetIntegral H μH f (QuotientGroup.mk x) =
      ∫ h : H, f (x * (h : G)) ∂μH := by sorry

end RiemannMasullo
