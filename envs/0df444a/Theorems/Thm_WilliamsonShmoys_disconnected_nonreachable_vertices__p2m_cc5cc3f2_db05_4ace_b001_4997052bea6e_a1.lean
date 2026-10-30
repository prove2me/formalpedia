-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- name    : WilliamsonShmoys.disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:51.802881+00:00
-- url     : https://prove2.me/theorems/e8119ebb-3d07-49f1-9a5a-76cb637c6969
-- title:
--   Disconnected finite graph has a nonreachable pair
-- statement:
--   A disconnected graph on at least three vertices has distinct vertices that are not connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Reachable u v := by sorry
