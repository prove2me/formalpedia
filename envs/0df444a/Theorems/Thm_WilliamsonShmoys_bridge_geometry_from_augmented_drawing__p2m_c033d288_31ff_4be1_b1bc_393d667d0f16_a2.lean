-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2
-- name    : WilliamsonShmoys.bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:02.050027+00:00
-- url     : https://prove2.me/theorems/19127b46-9641-4d27-850f-f6e2e566cd33
-- title:
--   Extract bridge geometry from an augmented planar drawing
-- statement:
--   Extract a simple bridge curve from the augmented drawing, oriented from x to y, avoiding vertices in its interior and meeting every original edge arc only at endpoints. The proof uses the added-edge arc in the order-compatible direction or reverses its parameter, then applies the drawing’s crossing property to original edges. Non-reachability excludes x = y and ensures the added pair is not an original edge; those facts cover the bridge edge and crossing boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_geometry_from_augmented_drawing__p2m_c033d288_31ff_4be1_b1bc_393d667d0f16_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v a b, u < v → a < b → H.Adj u v → H.Adj a b →
      (u, v) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc u v t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ u v, u < v → G.Adj u v →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t = arc u v s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
