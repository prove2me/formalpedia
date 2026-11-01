-- Prove2me | Theorems.Thm_WilliamsonShmoys_cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- name    : WilliamsonShmoys.cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:10.799187+00:00
-- url     : https://prove2.me/theorems/416996df-8a81-4fee-bdc7-c4c6da0092a4
-- title:
--   An edge-free cut separates its vertices by reachability
-- statement:
--   If no edge crosses from a set to its complement, a vertex in the set cannot be connected by a graph path to a vertex outside it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (S : Set V) (u v : V)
    (hu : u ∈ S) (hv : v ∉ S)
    (hcut : ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b) :
    ¬ G.Reachable u v := by
  sorry
