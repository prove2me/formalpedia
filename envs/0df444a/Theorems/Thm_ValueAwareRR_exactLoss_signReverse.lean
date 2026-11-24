-- Prove2me | Theorems.Thm_ValueAwareRR_exactLoss_signReverse
-- name    : ValueAwareRR.exactLoss_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:49.513426+00:00
-- url     : https://prove2.me/theorems/e89cfac0-8c3c-4ab4-a698-c02d3e7bd914
-- title:
--   Value Aware RR: exact Loss sign Reverse
-- statement:
--   The Value Aware RR construction uses the exact Loss sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L215-L218
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L215-L218

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.exactLoss_signReverse (m : ℚ) (o : SignedOrder) :
    exactLoss m (signReverse o) = exactLoss m o := by sorry
