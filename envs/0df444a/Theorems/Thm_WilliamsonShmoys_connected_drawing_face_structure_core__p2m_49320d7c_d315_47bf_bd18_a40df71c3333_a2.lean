-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2
-- name    : WilliamsonShmoys.connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:56.33268+00:00
-- url     : https://prove2.me/theorems/371329db-5f3f-48e1-a25d-9534580722f0
-- title:
--   Face structure from a connected crossing-free drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn, construct a finite set of faces and assign each dart to a face so that Euler’s relation holds and every face receives at least three darts, counted with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (hcard : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Type) (hF : Fintype F) (hFdec : DecidableEq F) (face : K.Dart → F),
      (letI : Fintype F := hF
       letI : DecidableEq F := hFdec
       Fintype.card V + Fintype.card F = K.edgeFinset.card + 2 ∧
       (∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f})) := by sorry
