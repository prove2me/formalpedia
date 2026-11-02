-- Prove2me | Theorems.Thm_WilliamsonShmoys_added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
-- name    : WilliamsonShmoys.added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:46:40.535431+00:00
-- url     : https://prove2.me/theorems/136dfdd0-f581-4d7d-9e56-c4a51aaad6bd
-- title:
--   Orient the added edge arc as a simple bridge
-- statement:
--   Orient the added edge arc from `u` to `v` and prove it is continuous and injective, has the required endpoints, and avoids every vertex location in its interior.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.added_edge_arc_is_oriented_bridge__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hnot : ¬ H.Reachable u v) :
    let bridge : ℝ → ℝ × ℝ := if u < v then arc u v else fun t => arc v u (1 - t)
    ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
    Set.InjOn bridge (Set.Icc 0 1) ∧
    bridge 0 = p u ∧ bridge 1 = p v ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) := by sorry
