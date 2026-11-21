-- Prove2me | Theorems.Thm_RiemannMasullo_equivalentCauchyNets_iff_of_tendsto
-- name    : RiemannMasullo.equivalentCauchyNets_iff_of_tendsto
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:30:35.520906+00:00
-- url     : https://prove2.me/theorems/09981abf-564a-4cb9-b26d-22f12914013b
-- title:
--   Equivalent convergent Cauchy nets have the same limit
-- statement:
--   Two convergent nets in a Hausdorff uniform additive group are equivalent Cauchy nets precisely when their limits coincide.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L90-L100

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo
universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J K : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  [Preorder K] [Nonempty K] [IsDirectedOrder K]

namespace RiemannMasullo

theorem equivalentCauchyNets_iff_of_tendsto [T2Space E] {f : J → E} {g : K → E} {x y : E}
    (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) :
    EquivalentCauchyNets f g ↔ x = y := by sorry

end RiemannMasullo
