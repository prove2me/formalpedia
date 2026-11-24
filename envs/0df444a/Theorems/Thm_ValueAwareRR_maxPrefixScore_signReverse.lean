-- Prove2me | Theorems.Thm_ValueAwareRR_maxPrefixScore_signReverse
-- name    : ValueAwareRR.maxPrefixScore_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:55:00.734344+00:00
-- url     : https://prove2.me/theorems/0a17c8ba-c34f-42ea-b80d-ef90b241cd3f
-- title:
--   Value Aware RR: max Prefix Score sign Reverse
-- statement:
--   The Value Aware RR construction uses the max Prefix Score sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L220-L224
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L220-L224

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.maxPrefixScore_signReverse (m : ℚ) (o : SignedOrder) :
    maxPrefixScore m (signReverse o) = maxPrefixScore m o := by sorry
