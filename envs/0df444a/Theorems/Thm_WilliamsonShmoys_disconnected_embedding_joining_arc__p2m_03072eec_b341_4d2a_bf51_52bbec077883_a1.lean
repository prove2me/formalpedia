-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- name    : WilliamsonShmoys.disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:43.526843+00:00
-- url     : https://prove2.me/theorems/f5d9ac23-37a8-4813-be64-33098d8dbd1e
-- title:
--   Joining distinct components through the unbounded face
-- statement:
--   For a finite disconnected graph with a crossing-free drawing, find two ordered, nonadjacent vertices and a simple continuous arc joining them whose interior misses every drawn vertex and every existing edge arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_embedding_joining_arc__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ u v, u < v → K.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hdis : ¬ K.Connected) :
    ∃ (u v : V) (gamma : ℝ → ℝ × ℝ),
      u < v ∧ ¬ K.Adj u v ∧
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) := by sorry
