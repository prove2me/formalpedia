-- Prove2me | Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered_div_nine
-- name    : ValueAwareRR.directEndpoint_eq_filtered_div_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:11.476865+00:00
-- url     : https://prove2.me/theorems/ea73d529-a822-49c3-87ef-c234ce56b099
-- title:
--   Value Aware RR: direct Endpoint eq filtered div nine
-- statement:
--   With `eta = 1/3`, every four-step endpoint is exactly `S_pi/9`.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L242-L246
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L242-L246

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.directEndpoint_eq_filtered_div_nine (m : ℚ) (o : SignedOrder) :
    directEndpoint m o = filteredSum m o / 9 := by sorry
