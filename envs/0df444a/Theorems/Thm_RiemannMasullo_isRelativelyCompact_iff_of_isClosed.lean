-- Prove2me | Theorems.Thm_RiemannMasullo_isRelativelyCompact_iff_of_isClosed
-- name    : RiemannMasullo.isRelativelyCompact_iff_of_isClosed
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:30:19.412663+00:00
-- url     : https://prove2.me/theorems/83e2e825-f596-43ee-88f8-5165838e091a
-- title:
--   Relative compactness of closed subsets
-- statement:
--   A closed subset of a Hausdorff topological space is relatively compact precisely when it is compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L189-L191

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo

namespace RiemannMasullo

theorem isRelativelyCompact_iff_of_isClosed {E : Type*} [TopologicalSpace E] [T2Space E]
    {A : Set E} (hA : IsClosed A) : IsRelativelyCompact A ↔ IsCompact A := by sorry

end RiemannMasullo
