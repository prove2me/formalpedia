-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_extension_by_ncard
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_extension_by_ncard
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:25:22.375871+00:00
-- url     : https://prove2.me/theorems/df62e182-9d28-4f63-a2a4-e5ec66202950
-- title:
--   Maximal drawable extension by edge count
-- statement:
--   A drawable finite simple graph has a drawable supergraph on the same vertices whose edge count is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_extension_by_ncard
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
