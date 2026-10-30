-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- name    : WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:30.155494+00:00
-- url     : https://prove2.me/theorems/6ebb6941-3575-43d9-99fa-a3f3a344e2d8
-- title:
--   Extract the oriented bridge arc
-- statement:
--   Construct the curve from the added H-edge, oriented from x to y, and retain its continuity, injectivity, endpoints, and avoidance of vertex points in its interior. Also record its pointwise representation so the second child can transfer the crossing property. The statement follows from the target hypotheses and the drawing definition. A proof splits on x < y, using non-reachability to rule out x = y; it obtains H adjacency of the added pair from hrel, then uses either the edge arc directly or the reversed parametrization t ↦ 1 - t. The reverse case transports interval membership, continuity, injectivity, endpoints, and interior avoidance. This removes curve selection and orientation bookkeeping from the parent. Its remaining core is elementary order reasoning and parameter reversal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hrel : ∀ u v, H.Adj u v ↔
      G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t = if x < y then arc x y t else arc y x (1 - t)) := by sorry
