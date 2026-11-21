-- Prove2me | Theorems.Thm_RiemannMasullo_isVonNBounded_iff_rescale
-- name    : RiemannMasullo.isVonNBounded_iff_rescale
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:30:21.960368+00:00
-- url     : https://prove2.me/theorems/590ce235-dab8-4e00-84bc-cb239cd95437
-- title:
--   Von Neumann boundedness by nonzero rescaling
-- statement:
--   A subset of a complex topological vector space is von Neumann bounded if and only if each neighborhood of zero contains a nonzero scalar multiple of the set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L156-L169

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo

namespace RiemannMasullo

theorem isVonNBounded_iff_rescale {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ U ∈ 𝓝 (0 : E), ∃ c : ℂ, c ≠ 0 ∧ c • B ⊆ U := by sorry

end RiemannMasullo
