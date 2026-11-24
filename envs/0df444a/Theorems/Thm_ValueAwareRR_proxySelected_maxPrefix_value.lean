-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_maxPrefix_value
-- name    : ValueAwareRR.proxySelected_maxPrefix_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:09:55.130193+00:00
-- url     : https://prove2.me/theorems/c90a7388-6cc1-45a7-aa9e-267463b76ed1
-- title:
--   Value Aware RR: proxy Selected max Prefix value
-- statement:
--   The Value Aware RR construction uses the proxy Selected max Prefix value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L412-L414
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L412-L414

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_maxPrefix_value (m : ℚ) (hm : 2 ≤ m) :
    maxPrefixScore m proxySelectedOrder = 2 * m := by sorry
