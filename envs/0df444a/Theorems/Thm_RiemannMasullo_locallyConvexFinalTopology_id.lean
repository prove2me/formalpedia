-- Prove2me | Theorems.Thm_RiemannMasullo_locallyConvexFinalTopology_id
-- name    : RiemannMasullo.locallyConvexFinalTopology_id
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:37:46.453069+00:00
-- url     : https://prove2.me/theorems/c5a279f5-f150-48a5-80c6-d5d69714fcc8
-- title:
--   Final locally convex topology of the identity map
-- statement:
--   For a polynormable complex space the final locally convex topology for the single identity map is its original topology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L245-L253

import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {ι : Type*} {X : ι → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

namespace RiemannMasullo

theorem locallyConvexFinalTopology_id [t : TopologicalSpace E] [PolynormableSpace ℂ E] :
    locallyConvexFinalTopology (X := fun _ : Unit ↦ E) (fun _ ↦ LinearMap.id) = t := by sorry

end RiemannMasullo
