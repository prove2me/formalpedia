-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_free_arc
-- name    : WilliamsonShmoys.disconnected_drawing_has_free_arc
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T06:16:54.071809+00:00
-- url     : https://prove2.me/theorems/38c8e422-db99-4279-ad13-20e21e69aef3
-- title:
--   Find a free arc between distinct components
-- statement:
--   For a finite disconnected graph with the specified planar drawing, select vertices in distinct connected components and exhibit, in the same drawing, a simple connecting arc whose interior avoids all vertices and which meets each existing edge arc only at an endpoint.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_has_free_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
      ∃ p : V → ℝ × ℝ, ∃ arc : V → V → ℝ → ℝ × ℝ,
        WilliamsonShmoys.IsPlanarDrawingData G p arc ∧
        WilliamsonShmoys.HasFreeConnectingArc G p arc u v := by sorry
