-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_endpoint
-- name    : ValueAwareRR.trueOptimal_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:08:07.127795+00:00
-- url     : https://prove2.me/theorems/40f65a78-6bf8-4799-a8d4-b2340b66dde6
-- title:
--   Value Aware RR: true Optimal endpoint
-- statement:
--   The Value Aware RR construction uses the true Optimal endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L296-L299
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L296-L299

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_endpoint (m : ℚ) :
    directEndpoint m trueOptimalOrder = 10 / 81 := by sorry
