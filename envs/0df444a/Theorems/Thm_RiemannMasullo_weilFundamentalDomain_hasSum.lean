-- Prove2me | Theorems.Thm_RiemannMasullo_weilFundamentalDomain_hasSum
-- name    : RiemannMasullo.weilFundamentalDomain_hasSum
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:20:38.794835+00:00
-- url     : https://prove2.me/theorems/38ae2133-0637-45c6-87a7-08888cf0705c
-- title:
--   Integration over the translates of a Borel fundamental domain
-- statement:
--   For an integrable function on a second-countable locally compact abelian group, its integrals over the translates of a Borel fundamental domain for a closed discrete subgroup sum to the group integral.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L217-L219

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
include hH hΔ hbij

namespace RiemannMasullo

theorem weilFundamentalDomain_hasSum {f : G → ℂ} (hf : Integrable f μ) :
    HasSum (fun h : H ↦ ∫ x in (fun y : G ↦ y * (h : G)) '' Δ, f x ∂μ)
      (∫ x, f x ∂μ) := by sorry

end RiemannMasullo
