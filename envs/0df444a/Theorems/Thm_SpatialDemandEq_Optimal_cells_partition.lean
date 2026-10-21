-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_cells_partition
-- name    : SpatialDemandEq.Optimal.cells_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:10.753608+00:00
-- url     : https://prove2.me/theorems/e5aad960-0f6d-4534-a64f-9960187432cb
-- title:
--   p. 8 and proof of Theorem 2, p. 10 — the weighted Voronoi cells A_k(w) partition S and Σ_k A_k(w) = 1 for any w
-- statement:
--   Under the standing assumptions of the spatial model (closed convex $\mathcal S \subseteq \mathbb R^n$; $\nu$ a probability measure on $\mathcal S$ absolutely continuous w.r.t. Lebesgue measure; a continuous metric $d$, facilities $x_1,\dots,x_K \in \mathcal S$ with $K \ge 1$, $d_k(x) = d(x,x_k)$ $\nu$-integrable and regular; $c, \lambda > 0$), for every weight vector $w \in \mathbb R^K$ the weighted Voronoi cells
--   $$\mathcal A_k(w) = \{x \in \mathcal S : d_k(x) + w_k \le d_j(x) + w_j \ \forall j \ne k\}$$
--   form a partition of $\mathcal S$ (measurable, covering $\mathcal S$, with $\nu$-null pairwise intersections), and
--   $$\sum_k A_k(w) = 1.$$
--
--   The identity $\sum_k A_k(w) = 1$ is the contradiction used in the uniqueness proof of Theorem 2; that the cells partition $\mathcal S$ is what makes any solution of (3) a decentralized equilibrium.
--
--   **Formalization Note** The regularity condition (the law of $d_j - d_k$ under $\nu$ has a density) is what makes the ties $\{d_j - d_k = w_k - w_j\}$ $\nu$-null.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 8 ('Such a diagram partitions a plane into regions around the locations x_1,...,x_K') and p. 10, proof of Theorem 2 ('Σ_k A_k(w) = 1 for any w')

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem cells_partition {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (w : Fin K → ℝ) :
    IsPartition ν S (cell S (distFn dst xs) w) ∧
      ∑ k, area ν (cell S (distFn dst xs) w k) = 1 := by sorry

end SpatialDemandEq.Optimal
