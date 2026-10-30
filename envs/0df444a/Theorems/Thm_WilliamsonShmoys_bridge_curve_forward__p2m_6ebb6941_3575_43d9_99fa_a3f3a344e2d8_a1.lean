-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
-- name    : WilliamsonShmoys.bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:42.045699+00:00
-- url     : https://prove2.me/theorems/30100382-419f-4b62-bbb0-2c6ab4bdaea4
-- title:
--   Extract a forward bridge arc
-- statement:
--   Extract the supplied arc for an H-edge whose endpoints are already in increasing order. Choose γ t = arc x y t and project each required property from hedge. This removes the forward case’s curve construction and property bookkeeping from the parent; its proof route is direct projection and simplification.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.bridge_curve_forward__p2m_6ebb6941_3575_43d9_99fa_a3f3a344e2d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (x y : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ u v, u < v → H.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hadj : H.Adj x y) (hlt : x < y) :
    ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = p x ∧ γ 1 = p y ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = arc x y t) := by sorry
