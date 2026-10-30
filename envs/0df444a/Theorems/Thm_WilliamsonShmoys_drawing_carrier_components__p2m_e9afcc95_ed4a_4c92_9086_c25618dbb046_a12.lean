-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- name    : WilliamsonShmoys.drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:02:11.423263+00:00
-- url     : https://prove2.me/theorems/188e1412-5b81-4b4f-8125-7b7ad68311d3
-- title:
--   Compact carrier and graph reachability of a noncrossing drawing
-- statement:
--   The carrier of a finite noncrossing drawing is compact. Two drawn vertices belong to the same connected component of the carrier exactly when they are reachable in the graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.drawing_carrier_components__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
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
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    IsCompact (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) ∧
      ∀ u v : V,
        p v ∈ connectedComponentIn (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) (p u) ↔
          G.Reachable u v := by
  sorry
