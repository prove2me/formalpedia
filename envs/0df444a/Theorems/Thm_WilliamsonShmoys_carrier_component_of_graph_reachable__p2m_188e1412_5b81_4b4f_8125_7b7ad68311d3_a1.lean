-- Prove2me | Theorems.Thm_WilliamsonShmoys_carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
-- name    : WilliamsonShmoys.carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:48.698789+00:00
-- url     : https://prove2.me/theorems/97929d67-691c-4fc1-9c5e-fd904455b6ca
-- title:
--   Graph paths lie in one carrier component
-- statement:
--   A graph path gives a connected path through the carrier, since each edge image is connected and joins the images of its endpoints. The reflexive graph path covers the zero-edge case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) :
    G.Reachable u v →
      p v ∈ connectedComponentIn
        (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) (p u) := by sorry
