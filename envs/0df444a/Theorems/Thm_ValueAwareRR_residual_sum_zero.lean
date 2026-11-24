-- Prove2me | Theorems.Thm_ValueAwareRR_residual_sum_zero
-- name    : ValueAwareRR.residual_sum_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:06:25.880915+00:00
-- url     : https://prove2.me/theorems/f97ae1be-36cf-48ee-ae12-99447d417f70
-- title:
--   Value Aware RR: residual sum zero
-- statement:
--   The Value Aware RR construction uses the residual sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L145-L148
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L145-L148

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.residual_sum_zero (m : ℚ) :
    residual m 0 + residual m 1 + residual m 2 + residual m 3 = 0 := by sorry
