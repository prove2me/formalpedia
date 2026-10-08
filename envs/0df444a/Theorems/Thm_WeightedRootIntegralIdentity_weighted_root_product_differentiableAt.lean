-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_product_differentiableAt
-- name    : WeightedRootIntegralIdentity.weighted_root_product_differentiableAt
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:30:24.434923+00:00
-- url     : https://prove2.me/theorems/ecf69a85-7baa-4ea1-8bc1-a8f96118fe81
-- title:
--   Differentiability of a finite weighted-root product
-- statement:
--   A finite product of complex factor functions is differentiable at a point whenever every factor is differentiable there. This is the product-holomorphicity component needed on the slit keyhole domain.
-- source:
--   Finite-product closure of complex differentiability.

import Mathlib
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_product_differentiableAt (n : ℕ) (f : ℕ → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ Finset.range n, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun u => ∏ i ∈ Finset.range n, f i u) z := by sorry

end WeightedRootIntegralIdentity
