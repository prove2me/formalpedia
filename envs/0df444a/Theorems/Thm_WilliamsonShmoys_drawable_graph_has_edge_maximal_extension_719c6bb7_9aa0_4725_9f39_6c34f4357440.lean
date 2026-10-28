-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- name    : WilliamsonShmoys.drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:48:00.936799+00:00
-- url     : https://prove2.me/theorems/860f0a3e-adc1-492f-991c-79210863c53c
-- title:
--   A drawable graph has an edge-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices with no drawable proper supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
