-- Prove2me | Theorems.Thm_WilliamsonShmoys_cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- name    : WilliamsonShmoys.cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:31:41.48297+00:00
-- url     : https://prove2.me/theorems/144b642d-7706-43bd-a144-ab46103a2af1
-- title:
--   An edge-free cut separates reachability
-- statement:
--   If every edge has both endpoints on the same side of a vertex cut, a vertex in the cut cannot be reachable from a vertex outside it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.cut_separates_reachability__p2m_eb8f4cd8_f0b2_4542_934a_57c382c5e901_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (s : Set V)
    (hu : u ∈ s) (hv : v ∉ s)
    (hcut : ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s)) :
    ¬ G.Reachable u v := by sorry
