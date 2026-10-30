-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- name    : WilliamsonShmoys.disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:41.322585+00:00
-- url     : https://prove2.me/theorems/282a2a61-c7fa-4a1e-ac79-616c5409586a
-- title:
--   A disconnected planar graph has a strict planar extension
-- statement:
--   A nonempty disconnected graph with a crossing-free drawing has a strict planar supergraph on the same vertices. Choose endpoints in distinct components and add an arc through the unbounded face to join them; the parent applies this to a maximal planar supergraph, where any such strict extension contradicts maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_strict_extension__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 0 < Fintype.card V)
    (hdisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ HasPlanarDrawingOn K := by sorry
