-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1
-- name    : WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:17.884226+00:00
-- url     : https://prove2.me/theorems/71ebc69f-78e1-4174-9ed9-e68a3e8da3bb
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   A disconnected graph on a finite linearly ordered vertex type with at least three vertices, if it has a crossing-free drawing, has a strict supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) (hdisconn : ¬ N.Connected) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by sorry
