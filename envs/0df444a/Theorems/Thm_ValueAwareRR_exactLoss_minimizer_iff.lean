-- Prove2me | Theorems.Thm_ValueAwareRR_exactLoss_minimizer_iff
-- name    : ValueAwareRR.exactLoss_minimizer_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:00:39.411807+00:00
-- url     : https://prove2.me/theorems/0023119d-a008-436d-9286-a5ce775148d6
-- title:
--   Value Aware RR: exact Loss minimizer iff
-- statement:
--   The two exact-loss minimizers, expressed as an equality of the argmin set.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L417-L426
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L417-L426

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.exactLoss_minimizer_iff (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    exactLoss m o = exactLoss m trueOptimalOrder ↔
      o = trueOptimalOrder ∨ o = signReverse trueOptimalOrder := by sorry
