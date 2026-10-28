-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:26:24.258624+00:00
-- url     : https://prove2.me/theorems/1aad81a2-ffc1-486e-a5cd-7c6b31189477
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied planar drawing has at most `3V − 6` edges. This replaces the target’s face-boundary inequality with a reusable graph-only bound. A proof route is to extend the drawing to an inclusion-maximal drawable simple graph on the same vertices, establish that its faces are triangular, count edge-face incidences, and apply Euler’s formula. The hypothesis `3 ≤ |V|` covers the smallest simple triangulation case and is essential to the stated bound’s range.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
