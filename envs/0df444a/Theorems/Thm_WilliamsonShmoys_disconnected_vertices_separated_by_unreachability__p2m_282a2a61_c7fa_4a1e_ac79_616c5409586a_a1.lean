-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
-- name    : WilliamsonShmoys.disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:44.668864+00:00
-- url     : https://prove2.me/theorems/1164846e-ab0a-4f8e-b56b-040383afdb64
-- title:
--   A nonempty disconnected graph has an unreachable pair
-- statement:
--   If a graph has at least one vertex and is disconnected, some two vertices are not joined by a walk. Nonemptiness matters because Mathlib's `Connected` includes a nonempty-vertex requirement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hne : Nonempty V) (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
