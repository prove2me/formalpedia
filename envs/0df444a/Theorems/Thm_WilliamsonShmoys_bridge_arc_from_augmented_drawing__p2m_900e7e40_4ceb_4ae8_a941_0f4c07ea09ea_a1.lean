-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
-- name    : WilliamsonShmoys.bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:47.946992+00:00
-- url     : https://prove2.me/theorems/c033d288-31ff-4be1-b1bc-393d667d0f16
-- title:
--   Extract a bridge arc from an augmented planar drawing
-- statement:
--   Given a planar drawing of a graph formed by adding exactly the edge between unreachable vertices `x` and `y`, use that edge’s arc as a bridge curve and restrict the drawing properties to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_arc_from_augmented_drawing__p2m_900e7e40_4ceb_4ae8_a941_0f4c07ea09ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (hH : HasPlanarDrawingOn H) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (γ : ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ u v, u < v → G.Adj u v →
          ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
        (∀ u v a b, u < v → a < b → G.Adj u v → G.Adj a b →
          (u, v) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc u v t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
        γ 0 = p x ∧ γ 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
        (∀ u v, u < v → G.Adj u v →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            γ t = arc u v s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) := by sorry
