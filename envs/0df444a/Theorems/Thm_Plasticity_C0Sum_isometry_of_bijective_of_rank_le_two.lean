-- Prove2me | Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two
-- name    : Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T18:59:38.172146+00:00
-- url     : https://prove2.me/theorems/0521bf39-9031-4834-9359-436ed2d30194
-- title:
--   Nonexpansive bijections between the unit balls of $c_0$ sums of spaces of dimension at most two are isometries
-- statement:
--   Let $(E_i)_{i\in I}$ and $(E'_k)_{k\in K}$ be families of real normed spaces over arbitrary index sets, with every $E_i$ and every $E'_k$ of dimension at most two (zero allowed), and let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms.
--   Every nonexpansive bijection $f\colon B_X\to B_Y$ between their closed unit balls is an isometry: $\|f(x)-f(y)\|=\|x-y\|$ for all $x,y\in B_X$.
--   The blocks may be zero, one-dimensional or planes with arbitrary norms (parallelograms, polygons, discs, mixtures of flat and curved boundary), with no uniformity over the index sets.
--
--   **Formalization Note** "Dimension at most two" is `Module.rank ℝ (E i) ≤ 2`, which excludes infinite-dimensional blocks.
-- source:
--   This repository: claim CUB109 (claims/cub.md), proof in expositions/c0_planes_with_scalars.md, with inputs CUB100, CUB101, CUB103, CUB106 and CUB108 (expositions/c0_one_general_plane.md, c0_separated_edge_planes.md, c0_planes_front.md, c0_planar_mixtures.md); finite index sets are also covered by Zavarzina, Ann. Funct. Anal. 9 (2018), Theorem 3.8

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem isometry_of_bijective_of_rank_le_two {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) (hE' : ∀ k, Module.rank ℝ (E' k) ≤ 2)
    (f : Metric.closedBall (0 : c0Sum E) 1 → Metric.closedBall (0 : c0Sum E') 1)
    (hf : LipschitzWith 1 f) (hbij : Function.Bijective f) : Isometry f := by sorry
end Plasticity.C0Sum
