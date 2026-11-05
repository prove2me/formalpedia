-- Prove2me | Theorems.Thm_WilliamsonShmoys_arc_count_strict_of_graph_strict__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2
-- name    : WilliamsonShmoys.arc_count_strict_of_graph_strict__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:32.60054+00:00
-- url     : https://prove2.me/theorems/d59618d8-3eb5-4197-bbca-f3753d61f13d
-- title:
--   Strict graph extension increases directed arc count
-- statement:
--   For a finite vertex type, a proper simple-graph extension strictly increases the number of directed adjacent vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.arc_count_strict_of_graph_strict__p2m_c50204fa_335d_4575_bac2_23cf83d1b5e4_a2
    {V : Type} [Fintype V]
    (K L : SimpleGraph V) (hKL : K ≤ L) (hne : K ≠ L) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // L.Adj p.1 p.2} := by sorry
