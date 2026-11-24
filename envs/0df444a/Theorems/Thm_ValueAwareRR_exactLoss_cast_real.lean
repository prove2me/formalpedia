-- Prove2me | Theorems.Thm_ValueAwareRR_exactLoss_cast_real
-- name    : ValueAwareRR.exactLoss_cast_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:07:59.338846+00:00
-- url     : https://prove2.me/theorems/49cfb7ec-151a-4bea-9635-8ce159003c26
-- title:
--   Value Aware RR: exact Loss cast real
-- statement:
--   The rational excess-loss identity likewise embeds unchanged into `ℝ`.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L267-L269
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L267-L269

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.exactLoss_cast_real (m : ℚ) (o : SignedOrder) :
    ((exactLoss m o : ℚ) : ℝ) = ((filteredSum m o : ℚ) : ℝ) ^ 2 / 162 := by sorry
