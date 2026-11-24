-- Prove2me | Theorems.Thm_PoincareFormalization_compactSpace_of_homotopyEquiv_sphere
-- name    : PoincareFormalization.compactSpace_of_homotopyEquiv_sphere
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T19:15:39.525271+00:00
-- url     : https://prove2.me/theorems/c1dda4a4-fab9-4c4f-9fda-4b43e2c93587
-- title:
--   A topological $n$-manifold homotopy equivalent to $\mathbb{S}^n$ is compact
-- statement:
--   Let $n \ge 1$, and let $M$ be a Hausdorff topological $n$-manifold without boundary (a charted space over $\mathbb{R}^n$). If $M$ is homotopy equivalent to the unit $n$-sphere $\mathbb{S}^n$,
--
--   $$M \simeq_h \mathbb{S}^n,$$
--
--   then $M$ is compact.
--
--   This captures the standard homological obstruction to non-compactness: any non-compact connected $n$-manifold without boundary has vanishing top-dimensional mod-$2$ singular homology $H_n(M; \mathbb{Z}/2\mathbb{Z}) = 0$, contradicting $H_n(M; \mathbb{Z}/2\mathbb{Z}) \cong H_n(\mathbb{S}^n; \mathbb{Z}/2\mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z}$.
--
--   **Formalization Note** Here $\mathbb{S}^n$ is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`, and no second-countability hypothesis is assumed on $M$.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Proposition 3.29, p. 236 (vanishing of top homology for non-compact manifolds) and Theorem 2.13, p. 114 (homology of spheres).

import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

open scoped ContinuousMap

namespace PoincareFormalization

theorem compactSpace_of_homotopyEquiv_sphere (n : ℕ) (hn : 1 ≤ n)
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    CompactSpace M := by
  sorry

end PoincareFormalization
