-- Prove2me | Theorems.Thm_RiemannMasullo_isWeilQuotientMeasure_bot
-- name    : RiemannMasullo.isWeilQuotientMeasure_bot
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:16:31.635873+00:00
-- url     : https://prove2.me/theorems/f3648f5d-4721-4667-919a-39a1716982a8
-- title:
--   Weil quotient measure for the trivial subgroup
-- statement:
--   For the trivial subgroup with counting measure, pushing forward the group Haar measure under the quotient map satisfies Weil's integral formula.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L175-L177

import Mathlib
import Definitions.Def_RiemannMasullo_WeilQuotient
open RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _

namespace RiemannMasullo

theorem isWeilQuotientMeasure_bot (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    IsWeilQuotientMeasure (⊥ : Subgroup G) μ Measure.count
      (μ.map (QuotientGroup.mk : G → G ⧸ (⊥ : Subgroup G))) := by sorry

end RiemannMasullo
