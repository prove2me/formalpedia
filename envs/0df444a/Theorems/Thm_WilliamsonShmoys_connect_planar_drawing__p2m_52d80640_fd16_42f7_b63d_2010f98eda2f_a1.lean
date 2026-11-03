-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- name    : WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:57.043522+00:00
-- url     : https://prove2.me/theorems/50046e68-ab20-4f6d-a7b5-2cf104147317
-- title:
--   Connect components of a planar drawing
-- statement:
--   Any drawing on a finite ordered vertex type with at least three vertices can be extended to a connected simple graph on the same vertices while retaining a drawing satisfying `HasPlanarDrawingOn`. The added arcs join components without crossing existing arcs except at shared endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
