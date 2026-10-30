-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- name    : WilliamsonShmoys.disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:13.45656+00:00
-- url     : https://prove2.me/theorems/24141c0a-e101-43b3-b89f-9504b9363753
-- title:
--   Connect a disconnected planar graph by a strict planar extension
-- statement:
--   A disconnected graph with the given planar drawing and at least three vertices has a strict connected planar supergraph on the same vertices. This isolates the geometric extension from the parent's edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ HasPlanarDrawingOn K ∧ K.Connected := by sorry
