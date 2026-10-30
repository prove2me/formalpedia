-- Prove2me | Theorems.Thm_WilliamsonShmoys_addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
-- name    : WilliamsonShmoys.addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:12.110658+00:00
-- url     : https://prove2.me/theorems/6d41a7cc-0330-45c8-a22c-836a8a445d01
-- title:
--   A certified noncrossing bridge yields a strict planar supergraph
-- statement:
--   Given an explicit drawing of H and a noncrossing simple arc between distinct nonadjacent vertices, add that edge to obtain a strict planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

theorem WilliamsonShmoys.addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hnotadj : ¬ H.Adj u v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by sorry
