-- Prove2me | Theorems.Thm_RiemannMasullo_isLimitSubspace_top
-- name    : RiemannMasullo.isLimitSubspace_top
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:37:44.296328+00:00
-- url     : https://prove2.me/theorems/76307f78-303d-4f2a-8ff6-15433a643289
-- title:
--   The full space is a limit subspace
-- statement:
--   For the given injective countable limit of Fréchet stages with Hausdorff target, the full submodule is a limit subspace.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L382-L416

import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

namespace RiemannMasullo

theorem isLimitSubspace_top [T2Space E] (hX : ∀ k, IsFrechetTVS (X k))
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] E} (h : IsInjectiveLCLimit j i) :
    IsLimitSubspace i ⊤ := by sorry

end RiemannMasullo
