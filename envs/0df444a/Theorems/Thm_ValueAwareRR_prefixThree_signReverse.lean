-- Prove2me | Theorems.Thm_ValueAwareRR_prefixThree_signReverse
-- name    : ValueAwareRR.prefixThree_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:20.812801+00:00
-- url     : https://prove2.me/theorems/d09fc029-1582-4645-b885-78514eb3922b
-- title:
--   Value Aware RR: prefix Three sign Reverse
-- statement:
--   The Value Aware RR construction uses the prefix Three sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L204-L207
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L204-L207

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.prefixThree_signReverse (m : ℚ) (o : SignedOrder) :
    prefixThree m (signReverse o) = -prefixThree m o := by sorry
