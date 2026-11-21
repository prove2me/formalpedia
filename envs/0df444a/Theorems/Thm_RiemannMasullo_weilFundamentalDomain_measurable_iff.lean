-- Prove2me | Theorems.Thm_RiemannMasullo_weilFundamentalDomain_measurable_iff
-- name    : RiemannMasullo.weilFundamentalDomain_measurable_iff
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:30:42.082093+00:00
-- url     : https://prove2.me/theorems/d74204ae-cc65-4969-bf53-521d2dace9c7
-- title:
--   Testing quotient measurability on a Borel fundamental domain
-- statement:
--   A complex function on the quotient is Borel measurable exactly when its pullback extended by zero outside a Borel fundamental domain is measurable.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L226-L227

import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _
variable (hH : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable [DiscreteTopology H] [SecondCountableTopology G]
variable {Δ : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))
variable (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)
include hH hΔ hbij hν

namespace RiemannMasullo

theorem weilFundamentalDomain_measurable_iff (f : G ⧸ H → ℂ) :
    Measurable f ↔ Measurable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) := by sorry

end RiemannMasullo
