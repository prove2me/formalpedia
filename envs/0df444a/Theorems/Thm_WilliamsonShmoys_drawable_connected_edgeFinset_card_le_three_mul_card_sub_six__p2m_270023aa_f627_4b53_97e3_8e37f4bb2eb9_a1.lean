-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- name    : WilliamsonShmoys.drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:47.166324+00:00
-- url     : https://prove2.me/theorems/849752b4-78ce-4d07-98c6-f3ea971ec2cd
-- title:
--   Connected planar drawing edge-count bound
-- statement:
--   A connected simple graph with a crossing-free drawing as defined by HasPlanarDrawingOn, on at least three vertices, has at most 3n−6 edges. This isolates the Euler formula and face-boundary counting obligation. It includes bridges and trees; the vertex lower bound is retained so the face-count argument applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
