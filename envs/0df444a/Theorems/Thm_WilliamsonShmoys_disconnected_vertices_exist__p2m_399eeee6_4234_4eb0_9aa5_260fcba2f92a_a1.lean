-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
-- name    : WilliamsonShmoys.disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:55.327186+00:00
-- url     : https://prove2.me/theorems/d106a26e-4986-45ee-803d-aa7d9ef8afc7
-- title:
--   Extract vertices in distinct components from disconnectedness
-- statement:
--   For a finite ordered vertex type, if not every pair of vertices is connected by a path, there is a pair that is not connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ ∀ u v, Relation.ReflTransGen G.Adj u v) :
    ∃ u v, ¬ Relation.ReflTransGen G.Adj u v := by sorry
