-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimalOrder_global_minimum
-- name    : ValueAwareRR.trueOptimalOrder_global_minimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:00:21.679805+00:00
-- url     : https://prove2.me/theorems/34e4e6fd-3a89-4514-8a8c-7158b4de56e3
-- title:
--   Value Aware RR: true Optimal Order global minimum
-- statement:
--   The Value Aware RR construction uses the true Optimal Order global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L428-L436
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L428-L436

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimalOrder_global_minimum (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    exactLoss m trueOptimalOrder ≤ exactLoss m o := by sorry
