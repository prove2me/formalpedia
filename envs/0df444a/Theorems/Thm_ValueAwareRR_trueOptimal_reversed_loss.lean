-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_reversed_loss
-- name    : ValueAwareRR.trueOptimal_reversed_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:09:23.70568+00:00
-- url     : https://prove2.me/theorems/4b36f24d-1a1a-409b-b29e-a514cbcf66ca
-- title:
--   Value Aware RR: true Optimal reversed loss
-- statement:
--   The Value Aware RR construction uses the true Optimal reversed loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L326-L328
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L326-L328

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_reversed_loss (m : ℚ) :
    exactLoss m (signReverse trueOptimalOrder) = 50 / 6561 := by sorry
