-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyhole_integrand_differentiableAt
-- name    : WeightedRootIntegralIdentity.keyhole_integrand_differentiableAt
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:38:31.709699+00:00
-- url     : https://prove2.me/theorems/3845016b-43af-42c0-9a33-376993d9b49b
-- title:
--   Local holomorphicity of the keyhole integrand away from zero
-- statement:
--   Away from the origin, the quotient of a finite weighted-root product by its complex variable is differentiable whenever each factor is differentiable.
-- source:
--   Finite-product differentiability and differentiability of division by a nonzero coordinate.

import Mathlib
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem keyhole_integrand_differentiableAt (n : ℕ) (f : ℕ → ℂ → ℂ) (z : ℂ)
    (hz : z ≠ 0)
    (hf : ∀ i ∈ Finset.range n, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun u => (∏ i ∈ Finset.range n, f i u) / u) z := by sorry

end WeightedRootIntegralIdentity
