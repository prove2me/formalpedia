-- Prove2me | Theorems.Thm_WilliamsonShmoys_admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- name    : WilliamsonShmoys.admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:10:48.433275+00:00
-- url     : https://prove2.me/theorems/d42a1f58-dfa3-4bd3-adbd-dd66bde730ff
-- title:
--   Extend a drawing across an admissible bridge arc
-- statement:
--   If K contains all old edges and, in canonical vertex order, has no edges except old edges and the new edge {u,v}, then the old drawing and admissible arc c give a crossing-free drawing of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.admissible_bridge_arc_addition_preserves_planarity__p2m_28fcd582_d200_46af_bf00_d4c58429d202_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ u v, u < v → G.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧ arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (u v : V)
    (huv : u < v ∧ ¬ G.Reachable u v)
    (c : ℝ → ℝ × ℝ)
    (hc : ContinuousOn c (Set.Icc 0 1) ∧
      Set.InjOn c (Set.Icc 0 1) ∧
      c 0 = p u ∧ c 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (K : SimpleGraph V)
    (hGK : G ≤ K)
    (hKedges : ∀ x y, x < y →
      (K.Adj x y ↔ (G.Adj x y ∨ (x = u ∧ y = v)))) :
    WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
