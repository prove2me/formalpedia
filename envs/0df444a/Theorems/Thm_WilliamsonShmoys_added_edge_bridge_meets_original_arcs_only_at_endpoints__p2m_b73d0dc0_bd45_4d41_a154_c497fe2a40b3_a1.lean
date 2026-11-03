-- Prove2me | Theorems.Thm_WilliamsonShmoys_added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- name    : WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:17.901296+00:00
-- url     : https://prove2.me/theorems/71b67d8a-24d4-4328-8243-ee4c563954c5
-- title:
--   The oriented added edge meets original arcs only at endpoints
-- statement:
--   Any intersection of the oriented added-edge arc with an original edge arc occurs at endpoints of both parametrizations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.added_edge_bridge_meets_original_arcs_only_at_endpoints__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hAugCross : ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hnot : ¬ H.Reachable u v)
    (bridge : ℝ → ℝ × ℝ)
    (hbridge : bridge = if u < v then arc u v else fun t => arc v u (1 - t)) :
    ∀ a b, a < b → H.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        bridge t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by sorry
