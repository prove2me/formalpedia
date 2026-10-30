-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_addable_bridge__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
-- name    : WilliamsonShmoys.disconnected_drawing_has_addable_bridge__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:54:36.311496+00:00
-- url     : https://prove2.me/theorems/1a7c0238-51ce-4df8-aecb-899d88b27460
-- title:
--   A disconnected plane drawing admits a noncrossing bridge
-- statement:
--   For a finite disconnected graph with at least three vertices and a crossing-free drawing, find a noncrossing simple arc joining vertices in distinct components, with its interior avoiding all drawn vertices and its intersections with existing edges restricted to compatible endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_drawing_has_addable_bridge__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ), Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ∃ u v c, u < v ∧ ¬ H.Adj u v ∧
        ContinuousOn c (Set.Icc 0 1) ∧
        Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p u ∧ c 1 = p v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
