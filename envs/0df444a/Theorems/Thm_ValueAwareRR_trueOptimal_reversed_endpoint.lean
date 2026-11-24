-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_reversed_endpoint
-- name    : ValueAwareRR.trueOptimal_reversed_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:08:50.330805+00:00
-- url     : https://prove2.me/theorems/f1ee2e18-bfdd-4983-b528-600c8ab983a4
-- title:
--   Value Aware RR: true Optimal reversed endpoint
-- statement:
--   The Value Aware RR construction uses the true Optimal reversed endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L316-L319
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L316-L319

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_reversed_endpoint (m : ℚ) :
    directEndpoint m (signReverse trueOptimalOrder) = -10 / 81 := by sorry
