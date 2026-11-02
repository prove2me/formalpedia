-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- name    : WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:05.904138+00:00
-- url     : https://prove2.me/theorems/19081e9f-d24f-471f-ab9e-3006005f0491
-- title:
--   A disconnected finite graph has vertices in different components
-- statement:
--   A finite graph with at least three vertices that is not connected has a pair of vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdisconn : ¬ N.Connected) :
    ∃ u v : V, ¬ N.Reachable u v := by sorry
