-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- name    : WilliamsonShmoys.connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:12:53.128019+00:00
-- url     : https://prove2.me/theorems/49320d7c-d315-47bf-bd18-a40df71c3333
-- title:
--   Face structure induced by a connected crossing-free drawing
-- statement:
--   The given drawing of a connected finite simple graph with at least three vertices induces a finite face set and a dart-to-face assignment satisfying Euler’s relation, a minimum of three darts counted at each face, and an exact count of all darts across faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (hcard : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Type) (hF : Fintype F) (hFdec : DecidableEq F) (face : K.Dart → F),
      (letI : Fintype F := hF
       letI : DecidableEq F := hFdec
       Fintype.card V + Fintype.card F = K.edgeFinset.card + 2 ∧
       (∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f}) ∧
       (∑ f : F, Fintype.card {d : K.Dart // face d = f}) = Fintype.card K.Dart) := by sorry
