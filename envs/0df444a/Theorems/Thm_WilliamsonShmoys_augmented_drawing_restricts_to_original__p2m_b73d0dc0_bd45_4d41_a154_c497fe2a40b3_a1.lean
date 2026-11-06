-- Prove2me | Theorems.Thm_WilliamsonShmoys_augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- name    : WilliamsonShmoys.augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:02.73838+00:00
-- url     : https://prove2.me/theorems/31d3bb4e-54e8-47f8-8c51-2509f4c3430b
-- title:
--   Restrict augmented drawing data to original edges
-- statement:
--   Every original edge retains its continuity, injectivity, endpoint, and interior vertex-avoidance drawing data from the augmented drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.augmented_drawing_restricts_to_original__p2m_b73d0dc0_bd45_4d41_a154_c497fe2a40b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) :
    ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w := by sorry
