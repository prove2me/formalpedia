-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- name    : WilliamsonShmoys.disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:32.677229+00:00
-- url     : https://prove2.me/theorems/7c92e097-26a8-4bba-9ade-61a98089220b
-- title:
--   Find a bridge arc between components of a finite plane drawing
-- statement:
--   Choose unreachable vertices in distinct components and a continuous injective arc between their drawing points. The arc’s interior avoids every vertex, and any intersection with an original edge arc occurs only at endpoints of both arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnectedDrawing_bridgeArc__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hG_not_connected : ¬ G.Connected) :
    ∃ u v : V, ∃ gamma : ℝ → ℝ × ℝ,
      u < v ∧ ¬ G.Reachable u v ∧
      ContinuousOn gamma (Set.Icc 0 1) ∧ Set.InjOn gamma (Set.Icc 0 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
          gamma t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
