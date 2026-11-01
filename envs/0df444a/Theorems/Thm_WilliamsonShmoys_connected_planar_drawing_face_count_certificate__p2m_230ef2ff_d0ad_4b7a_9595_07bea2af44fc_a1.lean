-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_certificate__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_face_count_certificate__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:52.672281+00:00
-- url     : https://prove2.me/theorems/7d630a3e-0460-4cb5-8d89-8a1ab8c13d2c
-- title:
--   Face-count certificate from a connected planar drawing
-- statement:
--   A crossing-free drawing of a finite connected simple graph with at least three vertices induces a finite set of faces whose count satisfies Euler’s formula, whose boundary lengths sum to twice the number of edges, and whose face boundary lengths are each at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open scoped BigOperators
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_face_count_certificate__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hconn : L.Connected) (hcard : 3 ≤ Fintype.card V) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; ∃ (F : ℕ) (ell : Fin F → ℕ), Fintype.card V + F = L.edgeFinset.card + 2 ∧ (∑ f : Fin F, ell f) = 2 * L.edgeFinset.card ∧ ∀ f, 3 ≤ ell f) := by sorry
