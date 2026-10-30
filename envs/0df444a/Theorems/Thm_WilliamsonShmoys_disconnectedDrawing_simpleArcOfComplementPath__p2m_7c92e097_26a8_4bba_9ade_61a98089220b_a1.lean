-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
-- name    : WilliamsonShmoys.disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:13.141365+00:00
-- url     : https://prove2.me/theorems/ff2db21c-4994-4086-b5ef-9d99edb0d1bf
-- title:
--   Simplify a path in the drawing complement
-- statement:
--   Given a continuous path whose interior avoids all vertices and edge arcs, replace it with an injective continuous arc with the same endpoints and avoidance properties. The edge-intersection conclusion then follows from interior avoidance and the edge hypotheses at endpoint parameters.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (u v : V) (huv : u < v) (hnot : ¬ G.Reachable u v)
    (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = p u ∧ delta 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
          delta t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
