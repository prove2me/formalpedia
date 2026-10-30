-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a1
-- name    : WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:00.962887+00:00
-- url     : https://prove2.me/theorems/2452be11-e3aa-4029-8e20-07e4b33157c6
-- title:
--   Extract the oriented bridge arc
-- statement:
--   Construct the curve from the augmented edge, oriented from x to y, and preserve its continuity, injectivity, endpoints, and avoidance of all vertex points in its interior. Also record its pointwise relation to the edge arc so the crossing-transfer lemma can use the correct orientation. The hypotheses come from the target and the drawing definition. Prove x ≠ y and ¬ G.Adj x y from non-reachability, obtain H adjacency of the added pair from hrel, then split on x < y. In the reverse-order case compose the arc with t ↦ 1 - t and transport interval membership, continuity, injectivity, endpoint values, and interior avoidance. This removes curve selection and orientation bookkeeping from the parent; the remaining work is elementary order and parameter-reversal reasoning.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_curve_without_crossings__p2m_19127b46_9641_4d27_850f_f6e2e566cd33_a1
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
