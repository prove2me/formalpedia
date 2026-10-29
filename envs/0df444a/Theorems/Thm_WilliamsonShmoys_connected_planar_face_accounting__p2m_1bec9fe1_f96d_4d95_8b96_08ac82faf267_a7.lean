-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
-- name    : WilliamsonShmoys.connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:26:29.820988+00:00
-- url     : https://prove2.me/theorems/87f8bddb-6da2-4d95-81aa-1f835ee1c5bb
-- title:
--   Euler and face incidence counts for a connected planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with the supplied crossing-free drawing, there is a face count satisfying Euler’s equation and the inequality that total face-boundary incidence is at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_accounting__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConn : N.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ f : Int,
      (Fintype.card V : Int) - (N.edgeSet.ncard : Int) + f = 2 ∧
      3 * f ≤ 2 * (N.edgeSet.ncard : Int) := by sorry
