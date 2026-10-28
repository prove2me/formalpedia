-- Prove2me | Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_add_edge_along_arc
-- name    : WilliamsonShmoys.crossing_free_drawing_add_edge_along_arc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:10:00.841265+00:00
-- url     : https://prove2.me/theorems/99b3478f-c46a-46d8-a34b-439e538e92dd
-- title:
--   Add a clean arc to a crossing-free drawing
-- statement:
--   Given a crossing-free drawing witness for G and a simple arc between distinct vertices u and v whose interior avoids every drawn vertex and every old edge, add the edge {u,v} and obtain a planar supergraph on the same vertices. The arc need not respect the vertex order; the proof orients it according to that order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.crossing_free_drawing_add_edge_along_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hbase : Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (γ : ℝ → ℝ × ℝ)
    (hγcont : ContinuousOn γ (Set.Icc 0 1))
    (hγinj : Set.InjOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = p u) (hγ1 : γ 1 = p v)
    (hγvert : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγedge : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t ≠ arc x y s) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Adj u v := by
  sorry
