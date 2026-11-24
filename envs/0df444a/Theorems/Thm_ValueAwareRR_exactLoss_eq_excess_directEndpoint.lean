-- Prove2me | Theorems.Thm_ValueAwareRR_exactLoss_eq_excess_directEndpoint
-- name    : ValueAwareRR.exactLoss_eq_excess_directEndpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:06:44.868441+00:00
-- url     : https://prove2.me/theorems/ce65ba27-1cbb-4954-b111-1121410fb151
-- title:
--   Value Aware RR: exact Loss eq excess direct Endpoint
-- statement:
--   The encoded terminal loss is the actual excess objective at the direct endpoint.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L249-L252
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L249-L252

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.exactLoss_eq_excess_directEndpoint (m : ℚ) (o : SignedOrder) :
    exactLoss m o = excessLoss (directEndpoint m o) := by sorry
