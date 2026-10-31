-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- name    : WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:01:41.146754+00:00
-- url     : https://prove2.me/theorems/e180e171-1461-4456-9297-ea94a0392a1c
-- title:
--   Euler count and face-boundary lengths from a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a list of facial boundary lengths. The number of boundaries satisfies Euler’s equation, their lengths sum to twice the edge count, and each length is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ f : ℕ, ∃ lengths : List ℕ,
      f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      lengths.length = f ∧
      lengths.sum = 2 * G.edgeSet.ncard ∧
      ∀ x ∈ lengths, 3 ≤ x := by sorry
