-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_87a22553
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_extension_87a22553
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:35:30.588055+00:00
-- url     : https://prove2.me/theorems/52bda59b-cf59-423f-b372-80d23c0ff3e1
-- title:
--   A finite drawable supergraph has a maximal drawable extension
-- statement:
--   Choose a maximum-edge drawable supergraph from the finite set of graphs on V. The original graph is among the candidates, so its edge count is no larger. Any drawable supergraph of the chosen graph must equal it, because a strict supergraph would have more edges. This argument also covers vertex types with fewer than three elements; no lower bound on |V| is needed for this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_maximal_extension_87a22553 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X) : ∃ H : SimpleGraph V, X ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ X.edgeSet.ncard ≤ H.edgeSet.ncard ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
