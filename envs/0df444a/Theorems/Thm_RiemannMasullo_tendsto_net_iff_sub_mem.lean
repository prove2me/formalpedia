-- Prove2me | Theorems.Thm_RiemannMasullo_tendsto_net_iff_sub_mem
-- name    : RiemannMasullo.tendsto_net_iff_sub_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:20:37.892183+00:00
-- url     : https://prove2.me/theorems/ae50a2f0-b718-40e1-a8cc-f73c182269f4
-- title:
--   Convergence of nets by differences
-- statement:
--   A net in a uniform additive group converges to a point precisely when its difference from that point eventually belongs to each neighborhood of zero.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L70-L73

import Mathlib

open Set Filter Topology TopologicalSpace Bornology

universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]

namespace RiemannMasullo

theorem tendsto_net_iff_sub_mem (f : J → E) (x : E) :
    Tendsto f atTop (𝓝 x) ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, x - f j ∈ U := by sorry

end RiemannMasullo
