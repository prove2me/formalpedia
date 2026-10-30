-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- name    : WilliamsonShmoys.disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:37.388072+00:00
-- url     : https://prove2.me/theorems/f215bd68-2d93-43b9-b08b-d2556e5d1303
-- title:
--   Extend a planar drawing using a bridge arc
-- statement:
--   Given an arc satisfying the bridge endpoint, continuity, injectivity, vertex avoidance, and edge-intersection conditions, add its endpoints as an edge and extend the drawing while preserving every original arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnectedDrawing_packageBridge__p2m_cf450bef_2e6f_4b2f_9b98_7a3039fc28c5_a2
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
    (hG_not_connected : ¬ G.Connected)
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v) (hreach : ¬ G.Reachable u v)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hcrossGamma : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
        gamma t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ H : SimpleGraph V, ∃ q : V → V → ℝ → ℝ × ℝ, ∃ a b,
      G ≤ H ∧ a < b ∧ ¬ G.Reachable a b ∧ H.Adj a b ∧ ¬ G.Adj a b ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ c d, c < d → H.Adj c d → (x, y) ≠ (c, d) →
          ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, q x y t = arc x y t) := by sorry
