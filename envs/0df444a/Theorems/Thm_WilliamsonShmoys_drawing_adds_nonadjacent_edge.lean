-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_adds_nonadjacent_edge
-- name    : WilliamsonShmoys.drawing_adds_nonadjacent_edge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:14:17.94693+00:00
-- url     : https://prove2.me/theorems/7c399724-55b1-402e-9f60-aa510efea16b
-- title:
--   A planar drawing can be extended across a missing edge
-- statement:
--   Given a drawing of a graph and distinct nonadjacent vertices, there is a planar drawable supergraph that adds the edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawing_adds_nonadjacent_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (u v : V)
    (huv : u ≠ v)
    (hnot : ¬ Q.Adj u v) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.Adj u v ∧ ¬ Q.Adj u v := by sorry
