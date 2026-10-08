-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_slitQuotientHolomorphicity
-- name    : WeightedRootIntegralIdentity.slitQuotientHolomorphicity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T11:18:26.522453+00:00
-- url     : https://prove2.me/theorems/8d252d2c-7a66-422f-a900-e9f4aadecbda
-- title:
--   Holomorphic quotient on the slit domain
-- statement:
--   If the branch numerator is differentiable on a domain avoiding zero, then dividing by z preserves differentiability there.

import Mathlib

theorem WeightedRootIntegralIdentity.slitQuotientHolomorphicity
    (G : ℂ → ℂ) (D : Set ℂ)
    (hG : DifferentiableOn ℂ G D)
    (hzero : ∀ z ∈ D, z ≠ 0) :
    DifferentiableOn ℂ (fun z => G z / z) D := by sorry
