-- Prove2me | Theorems.Thm_ValueAwareRR_prefixOne_signReverse
-- name    : ValueAwareRR.prefixOne_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:14.550532+00:00
-- url     : https://prove2.me/theorems/33ea02e0-4f79-43e3-b0aa-71f3c4b715ef
-- title:
--   Value Aware RR: prefix One sign Reverse
-- statement:
--   The Value Aware RR construction uses the prefix One sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L195-L197
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L195-L197

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.prefixOne_signReverse (m : ℚ) (o : SignedOrder) :
    prefixOne m (signReverse o) = -prefixOne m o := by sorry
