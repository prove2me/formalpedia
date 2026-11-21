-- Prove2me | Theorems.Thm_RiemannMasullo_weilFundamentalDomain_integral_eq
-- name    : RiemannMasullo.weilFundamentalDomain_integral_eq
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:32:49.075245+00:00
-- url     : https://prove2.me/theorems/c427d66f-c8b8-419c-a628-eacde1527413
-- title:
--   An invariant integral is independent of the fundamental domain
-- statement:
--   An integrable subgroup-invariant function on one Borel fundamental domain is integrable on any other, and the two integrals agree.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L244-L248

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
variable {Δ Δ' : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))
include hH hΔ hbij

namespace RiemannMasullo

theorem weilFundamentalDomain_integral_eq (hΔ' : MeasurableSet Δ')
    (hbij' : Function.Bijective (fun x : Δ' ↦ (QuotientGroup.mk x.val : G ⧸ H)))
    {f : G → ℂ} (hf : Measurable f) (hinv : ∀ (x : G) (h : H), f (x * (h : G)) = f x)
    (hint : IntegrableOn f Δ μ) :
    IntegrableOn f Δ' μ ∧ (∫ x in Δ, f x ∂μ) = ∫ x in Δ', f x ∂μ := by sorry

end RiemannMasullo
