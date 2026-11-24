-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedExactLoss_minimizer_iff
-- name    : ValueAwareRR.normalizedExactLoss_minimizer_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:03:31.865112+00:00
-- url     : https://prove2.me/theorems/e84976d0-4e57-416e-994f-2f8820e41a2f
-- title:
--   Value Aware RR: normalized Exact Loss minimizer iff
-- statement:
--   Positive common normalization preserves the exact-loss argmin set.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L646-L657
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L646-L657

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedExactLoss_minimizer_iff
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedExactLoss m o = normalizedExactLoss m trueOptimalOrder ↔
      o = trueOptimalOrder ∨ o = signReverse trueOptimalOrder := by sorry
