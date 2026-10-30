-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- name    : WilliamsonShmoys.bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:58.839577+00:00
-- url     : https://prove2.me/theorems/933effcb-b4de-4d08-8b10-7d85017559a8
-- title:
--   Extend the drawing across the added pair
-- statement:
--   Given a graph whose edges are exactly the old edges together with `{u,v}`, extend the arc family to all its edges while preserving every old arc and satisfying the drawing conditions for the augmented graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
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
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v) (hreach : ¬ G.Reachable u v)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hcrossGamma : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
        gamma t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (H : SimpleGraph V)
    (hAdj : ∀ x y, H.Adj x y ↔
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ q : V → V → ℝ → ℝ × ℝ,
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ c d, c < d → H.Adj c d → (x, y) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, q x y t = arc x y t) := by sorry
