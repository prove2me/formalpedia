-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedProxy_maxPrefix_global_minimum
-- name    : ValueAwareRR.normalizedProxy_maxPrefix_global_minimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:04:53.709719+00:00
-- url     : https://prove2.me/theorems/82b7d184-5f1e-46ce-a33b-62873ba2be2c
-- title:
--   Value Aware RR: normalized Proxy max Prefix global minimum
-- statement:
--   The Value Aware RR construction uses the normalized Proxy max Prefix global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L694-L701
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L694-L701

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedProxy_maxPrefix_global_minimum
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m proxySelectedOrder ≤ normalizedMaxPrefixScore m o := by sorry
