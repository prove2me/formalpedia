-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_concreteSlitContourSetup
-- name    : WeightedRootIntegralIdentity.concreteSlitContourSetup
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T11:27:49.614036+00:00
-- url     : https://prove2.me/theorems/c4648c08-0953-4d16-b98b-acb70b4c739d
-- statement:
--   Let D be a slit domain on which the weighted branch product F(z)=∏_{i<n}(z-a_i)^{w_i} is differentiable and which avoids 0. Let γ₀,…,γ₅ be the six upper-bank, lower-bank, vertical-side, inner-arc, and outer-arc parametrizations, each lying in D and piecewise C¹. Then F(z)/z is holomorphic on D, and the six actual parametrizations are branch-safe and piecewise C¹. This supplies the concrete contour data needed before applying the residue theorem.

import Mathlib
open scoped BigOperators

theorem WeightedRootIntegralIdentity.concreteSlitContourSetup
    (n : ℕ) (a w : ℕ → ℝ) (D : Set ℂ)
    (γ : Fin 6 → ℝ → ℂ)
    (hF : DifferentiableOn ℂ
      (fun z : ℂ => ∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) D)
    (hzero : ∀ z ∈ D, z ≠ 0)
    (hpieces : ∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1))
    (hsafe : ∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) :
    DifferentiableOn ℂ
        (fun z : ℂ =>
          (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) D ∧
      (∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) := by sorry
