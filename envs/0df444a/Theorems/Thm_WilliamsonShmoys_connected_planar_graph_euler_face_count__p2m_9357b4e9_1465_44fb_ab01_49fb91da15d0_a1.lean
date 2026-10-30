-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1
-- name    : WilliamsonShmoys.connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:44.127007+00:00
-- url     : https://prove2.me/theorems/f9c8d92b-3a05-45f0-b41b-64ba71ce8cc1
-- title:
--   Euler face count and incidence bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing admits a finite face count satisfying Euler's equation and the face-boundary incidence inequality. This removes the topological conversion and face counting from the parent; the parent needs only natural-number arithmetic. The exact positivity, connectedness, and drawing hypotheses are preserved. A proof route is to regard the finite family of injective noncrossing arcs as a plane embedding, take its cellular faces, apply Euler's formula, and count the two sides of each edge. Simplicity and the three-vertex condition ensure every face boundary walk has length at least three, including walks that traverse bridges twice. The remaining core obligation is formalizing this plane-embedding and face-boundary argument for the given continuous-arc definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by sorry
