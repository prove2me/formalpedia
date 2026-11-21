-- Prove2me | Theorems.Thm_RiemannMasullo_cauchySeq_iff_sub_mem
-- name    : RiemannMasullo.cauchySeq_iff_sub_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:20:36.474686+00:00
-- url     : https://prove2.me/theorems/5a89c371-6817-4895-9005-f97e26a703d0
-- title:
--   Cauchy nets by pairwise differences
-- statement:
--   A net indexed by a nonempty directed preorder is Cauchy precisely when every zero-neighborhood contains all differences of pairs of terms on a common tail.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L77-L81

import Mathlib

open Set Filter Topology TopologicalSpace Bornology

universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]

namespace RiemannMasullo

theorem cauchySeq_iff_sub_mem (f : J → E) :
    CauchySeq f ↔ ∀ U ∈ 𝓝 (0 : E), ∃ j₀, ∀ j ≥ j₀, ∀ k ≥ j₀, f j - f k ∈ U := by sorry

end RiemannMasullo
