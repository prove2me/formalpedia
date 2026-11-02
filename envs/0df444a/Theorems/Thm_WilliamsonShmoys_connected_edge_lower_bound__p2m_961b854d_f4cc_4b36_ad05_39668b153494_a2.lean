-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- name    : WilliamsonShmoys.connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:11.329603+00:00
-- url     : https://prove2.me/theorems/43bd5bf3-2b3b-4156-97a0-b86c41186075
-- title:
--   Connected graphs contain enough edges for a spanning tree
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeFinset.card + 1 := by sorry
