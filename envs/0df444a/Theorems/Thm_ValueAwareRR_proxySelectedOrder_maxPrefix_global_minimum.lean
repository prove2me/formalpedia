-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelectedOrder_maxPrefix_global_minimum
-- name    : ValueAwareRR.proxySelectedOrder_maxPrefix_global_minimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:01:34.120591+00:00
-- url     : https://prove2.me/theorems/137f3380-ca57-43ed-ba97-dfc6bdc68f09
-- title:
--   Value Aware RR: proxy Selected Order max Prefix global minimum
-- statement:
--   The Value Aware RR construction uses the proxy Selected Order max Prefix global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L464-L475
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L464-L475

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelectedOrder_maxPrefix_global_minimum
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    maxPrefixScore m proxySelectedOrder ≤ maxPrefixScore m o := by sorry
