-- Prove2me | Theorems.Thm_WilliamsonShmoys_clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
-- name    : WilliamsonShmoys.clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:17.024254+00:00
-- url     : https://prove2.me/theorems/3146b8f5-e959-485d-af27-a37e51e3ead3
-- title:
--   Stitch a clean joining arc into drawing data
-- statement:
--   For any simple graph L whose adjacency is exactly the old adjacency plus the undirected pair {u,v}, construct injective vertex positions and edge arcs satisfying the drawing and crossing conditions, using the supplied clean arc γ for the joining edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.clean_arc_drawing_geometry__p2m_a073dd38_4e30_4f95_9bdc_3dc54f59a882_a2
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
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s)
    (L : SimpleGraph V)
    (hL : ∀ a b, L.Adj a b ↔
      K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
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
