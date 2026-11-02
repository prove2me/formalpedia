-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
-- name    : WilliamsonShmoys.disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:35:27.021206+00:00
-- url     : https://prove2.me/theorems/0f8397c3-8159-41a4-b019-9aae9b74821e
-- title:
--   Select vertices in distinct components
-- statement:
--   For a disconnected graph on at least three vertices, there are distinct vertices that are not connected by a path. This removes the finite graph-theoretic witness selection from the parent; prove it from the definition of connectedness and the cardinality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_vertices__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V) (hdisc : ¬ G.Connected) : ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by sorry
