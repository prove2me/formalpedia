-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_loss
-- name    : ValueAwareRR.trueOptimal_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:07.670795+00:00
-- url     : https://prove2.me/theorems/19b9d389-d2fc-4e2b-9840-b5988d74c6e9
-- title:
--   Value Aware RR: true Optimal loss
-- statement:
--   The Value Aware RR construction uses the true Optimal loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L286-L288
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L286-L288

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_loss (m : ℚ) : exactLoss m trueOptimalOrder = 50 / 6561 := by sorry
