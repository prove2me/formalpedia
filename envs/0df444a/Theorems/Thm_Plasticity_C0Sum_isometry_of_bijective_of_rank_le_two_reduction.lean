-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_reduction
-- name    : Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.reduction
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:29.640878+00:00
-- url     : https://prove2.me/theorems/b1c07ec7-7faf-4f2c-b97a-2503c5c46309
-- title:
--   Every $c_0$ sum of spaces of dimension at most two is a $c_0$ sum of lines and non-parallelogram planes
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces over an arbitrary index set, each of dimension at most two (zero allowed).
--   There are an index set $J$ and a family $(G_j)_{j\in J}$ of real normed spaces, each of dimension $1$ or of dimension $2$ with a closed unit ball that has more than four extreme points, such that $c_0(J;G_j)$ and $c_0(I;E_i)$, with the supremum block norms, are linearly isometric.
--   The pieces come from dropping zero blocks and splitting each parallelogram block into two one-dimensional blocks.
--
--   **Formalization Note** "Dimension at most two" is `Module.rank ℝ (E i) ≤ 2`; the index type $J$ lives in the universe of $I$ and the spaces $G_j$ in that of the $E_i$, and the isometry is a `LinearIsometryEquiv` from `c0Sum G` to `c0Sum E`.
-- source:
--   This repository: claim CUB109 (claims/cub.md), expositions/c0_planes_with_scalars.md §4 (dropping zero blocks and splitting each parallelogram block into two scalar blocks)

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u v

namespace Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
theorem reduction {ι : Type u} (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) :
    ∃ (J : Type u) (G : J → Type v) (_ : ∀ j, NormedAddCommGroup (G j))
      (_ : ∀ j, NormedSpace ℝ (G j)),
      (∀ j, Module.finrank ℝ (G j) = 1 ∨ (Module.finrank ℝ (G j) = 2 ∧
        4 < (Set.extremePoints ℝ (Metric.closedBall (0 : G j) 1)).encard)) ∧
      Nonempty (c0Sum G ≃ₗᵢ[ℝ] c0Sum E) := by sorry
end Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
