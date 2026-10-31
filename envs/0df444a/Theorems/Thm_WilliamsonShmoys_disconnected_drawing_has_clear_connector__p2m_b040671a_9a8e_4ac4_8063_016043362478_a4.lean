-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_clear_connector__p2m_b040671a_9a8e_4ac4_8063_016043362478_a4
-- name    : WilliamsonShmoys.disconnected_drawing_has_clear_connector__p2m_b040671a_9a8e_4ac4_8063_016043362478_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:33.614282+00:00
-- url     : https://prove2.me/theorems/c3d43a36-7dd4-4756-9298-41334f71d846
-- title:
--   A disconnected drawing has a clear connector between components
-- statement:
--   A finite ordered disconnected graph with a planar drawing has explicit drawing data, two ordered nonadjacent vertices, and a simple arc joining their drawing points whose interior avoids every vertex and existing edge arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_has_clear_connector__p2m_b040671a_9a8e_4ac4_8063_016043362478_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hDisc : ¬ H.Connected) : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (u v : V) (c : ℝ → ℝ × ℝ), Function.Injective p ∧ (∀ x y, x < y → H.Adj x y → ContinuousOn (arc x y) (Set.Icc 0 1) ∧ Set.InjOn (arc x y) (Set.Icc 0 1) ∧ arc x y 0 = p x ∧ arc x y 1 = p y ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧ (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b → (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧ u < v ∧ ¬ H.Adj u v ∧ ContinuousOn c (Set.Icc (0 : ℝ) 1) ∧ Set.InjOn c (Set.Icc (0 : ℝ) 1) ∧ c 0 = p u ∧ c 1 = p v ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧ (∀ x y, x < y → H.Adj x y → ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, c t ≠ arc x y s) := by sorry
