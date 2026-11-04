-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- name    : WilliamsonShmoys.connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:03.776247+00:00
-- url     : https://prove2.me/theorems/87b40329-c584-43e3-b2a8-a209b09780ca
-- title:
--   Connected planar drawing yields facial boundary data and Euler’s equation
-- statement:
--   Construct a finite face count and boundary lengths from the explicit drawing. Their sum counts each edge twice, each face boundary has length at least three, and the vertex, face, and edge counts satisfy Euler’s equation. Connectedness is needed for this Euler relation; simplicity and the lower bound on vertices support the boundary-length condition, including in the presence of bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ faceCount : Nat,
      (∃ boundaryLength : Fin faceCount → Nat,
        (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
        (∀ f : Fin faceCount, 3 ≤ boundaryLength f)) ∧
      Fintype.card V + faceCount = K.edgeFinset.card + 2 := by
  sorry
