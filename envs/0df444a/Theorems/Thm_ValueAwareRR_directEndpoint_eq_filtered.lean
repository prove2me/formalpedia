-- Prove2me | Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered
-- name    : ValueAwareRR.directEndpoint_eq_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:55:03.929509+00:00
-- url     : https://prove2.me/theorems/834fa4d8-3639-458f-84eb-c0ea44ecdb11
-- title:
--   Value Aware RR: direct Endpoint eq filtered
-- statement:
--   The direct recurrence and filtered-prefix endpoint agree on all 24 orders.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L233-L239
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L233-L239

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.directEndpoint_eq_filtered (m : ℚ) (o : SignedOrder) :
    directEndpoint m o = stepSize ^ 2 * filteredSum m o := by sorry
