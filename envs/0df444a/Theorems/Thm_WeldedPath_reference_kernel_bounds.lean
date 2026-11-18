-- Prove2me | Theorems.Thm_WeldedPath_reference_kernel_bounds
-- name    : WeldedPath.reference_kernel_bounds
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T20:57:27.142188+00:00
-- url     : https://prove2.me/theorems/90c7e9fb-cf2b-4b23-9f60-fea76f6f2864
-- title:
--   Structural bounds for the welded-tree reference kernels
-- statement:
--   For every valid properly three-colored welded-tree instance with n>=16 and 2<=l<=n-4, each reference kernel kappa_alpha is symmetric and has all row and column sums over the finite label range at most one. Every transition from a weld vertex has point mass at most 4/2^n. At every vertex in V_mid all three colors have defined permuted-edge data. These statements concern the actual graph-defined kernel and do not assume any stochastic-kernel or conditional-distribution estimate.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS1, the reference weights in equation (50), supporting the free-transition estimates in Section 4.1. The elementary class-size ingredient corresponds to Lemma 3.2 and the edge-class counts in Section 3.1. The supplied proof establishes this explicit structural intermediate directly from the published definitions.

import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath

open Classical Supplement
open scoped BigOperators

theorem reference_kernel_bounds :
    ∀ n l : ℕ, 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
      (∀ (α : Fin 3) (u v : ℕ), kappa l G α u v = kappa l G α v u) ∧
      (∀ (α : Fin 3) (u : ℕ), (∑ v : Label n, kappa l G α u v.1) ≤ 1) ∧
      (∀ (α : Fin 3) (v : ℕ), (∑ u : Label n, kappa l G α u.1 v) ≤ 1) ∧
      (∀ u ∈ Vweld n, ∀ (α : Fin 3) (v : ℕ),
        kappa l G α u v ≤ 4 / (2 : ℝ) ^ n) ∧
      (∀ u ∈ Vmid n l, ∀ α : Fin 3, permData l G u α ≠ none) := by
  sorry

end WeldedPath
