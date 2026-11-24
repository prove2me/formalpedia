-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedTrueOptimal_global_minimum
-- name    : ValueAwareRR.normalizedTrueOptimal_global_minimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:04:35.897467+00:00
-- url     : https://prove2.me/theorems/04843d71-3807-498e-b9e9-34866e345d7c
-- title:
--   Value Aware RR: normalized True Optimal global minimum
-- statement:
--   The Value Aware RR construction uses the normalized True Optimal global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L688-L692
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L688-L692

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedTrueOptimal_global_minimum
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedExactLoss m trueOptimalOrder ≤ normalizedExactLoss m o := by sorry
