-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
-- name    : WilliamsonShmoys.disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:08:22.977297+00:00
-- url     : https://prove2.me/theorems/14a3f77f-68b8-4d06-86d5-54f2c723cf69
-- title:
--   A disconnected graph yields an ordered unreachable pair and separating cut
-- statement:
--   A finite linearly ordered disconnected graph with at least three vertices has an ordered pair in different reachability components, with no edge between them, and a vertex set separating the pair with no edges crossing the cut. To prove it, take a vertex’s reachable component for the set; adjacency across the cut would extend reachability. The size hypothesis is retained from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ u v : V, ∃ S : Set V,
      u < v ∧
      ¬ G.Reachable u v ∧
      ¬ G.Adj u v ∧
      u ∈ S ∧
      v ∉ S ∧
      (∀ a b : V, a ∈ S → b ∉ S → ¬ G.Adj a b) := by sorry
