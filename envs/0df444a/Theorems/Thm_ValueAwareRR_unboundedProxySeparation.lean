-- Prove2me | Theorems.Thm_ValueAwareRR_unboundedProxySeparation
-- name    : ValueAwareRR.unboundedProxySeparation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:13:14.067685+00:00
-- url     : https://prove2.me/theorems/a28d68b3-3262-4f95-8ae1-726e24621e2b
-- title:
--   Value Aware RR: unbounded Proxy Separation
-- statement:
--   Headline theorem: even after uniform residual normalization, both proxy argmin
--   sets select the same two orders, their exact-loss ratio is unbounded, and the
--   true optimum remains strictly positive on every finite family member.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L798-L808
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L798-L808

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.unboundedProxySeparation :
    (∀ m : ℕ, 2 ≤ m → NaturalFamilyCertificate m) ∧
      ∀ N : ℕ, ∃ m : ℕ,
        2 ≤ m ∧ NaturalFamilyCertificate m ∧
          (N : ℚ) ≤ normalizedLossRatio (m : ℚ) := by sorry
