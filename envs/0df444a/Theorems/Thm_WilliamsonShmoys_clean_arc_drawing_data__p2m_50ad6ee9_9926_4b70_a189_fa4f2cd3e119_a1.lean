-- Prove2me | Theorems.Thm_WilliamsonShmoys_clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
-- name    : WilliamsonShmoys.clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:04.023955+00:00
-- url     : https://prove2.me/theorems/a073dd38-4e30-4f95-9bdc-3dc54f59a882
-- title:
--   Extend drawing witnesses by a clean joining arc
-- statement:
--   Given the existing drawing witnesses and the supplied clean joining arc, construct a graph with exactly the old edges plus {u,v}, together with raw vertex and edge drawing witnesses satisfying the continuity, injectivity, endpoint, vertex-avoidance, and crossing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.clean_arc_drawing_data__p2m_50ad6ee9_9926_4b70_a189_fa4f2cd3e119_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ x y, x < y → K.Adj x y →
      ContinuousOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc x y) (Set.Icc (0 : ℝ) 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hcross : ∀ x y a b, x < y → a < b → K.Adj x y → K.Adj a b →
      (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc x y t = arc a b s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (harcs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      (∀ a b, L.Adj a b ↔
        K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      ∃ (q : V → ℝ × ℝ) (β : V → V → ℝ → ℝ × ℝ),
        Function.Injective q ∧
        (∀ x y, x < y → L.Adj x y →
          ContinuousOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (β x y) (Set.Icc (0 : ℝ) 1) ∧
          β x y 0 = q x ∧ β x y 1 = q y ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, β x y t ≠ q w) ∧
        (∀ x y a b, x < y → a < b → L.Adj x y → L.Adj a b →
          (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, β x y t = β a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
