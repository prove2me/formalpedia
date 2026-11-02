-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:42.156176+00:00
-- url     : https://prove2.me/theorems/86e10b2c-611f-45b0-95e3-96a657357242
-- title:
--   Euler edge bound for connected drawn graphs
-- statement:
--   For a connected finite simple graph on at least three vertices, a drawing satisfying `HasPlanarDrawingOn` implies the Euler edge bound. The proof route is to derive a plane embedding from the injective continuous arcs, apply Euler's formula, and bound the total facial boundary-walk length below by three per face. This isolates the topological core; connected trees are included because their facial walks count bridges twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected) (hplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
