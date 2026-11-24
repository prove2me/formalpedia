-- Prove2me | Theorems.Thm_ValueAwareRR_exactLoss_eq_filtered_square
-- name    : ValueAwareRR.exactLoss_eq_filtered_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:00:01.516662+00:00
-- url     : https://prove2.me/theorems/b8339995-c8e3-428a-8869-282a0a5b726e
-- title:
--   Value Aware RR: exact Loss eq filtered square
-- statement:
--   For every one of the twenty-four orders, terminal excess loss is `S_pi^2/162`.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L255-L259
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L255-L259

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.exactLoss_eq_filtered_square (m : ℚ) (o : SignedOrder) :
    exactLoss m o = filteredSum m o ^ 2 / 162 := by sorry
