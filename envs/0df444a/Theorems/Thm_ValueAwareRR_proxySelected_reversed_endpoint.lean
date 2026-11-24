-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_reversed_endpoint
-- name    : ValueAwareRR.proxySelected_reversed_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:09:00.582279+00:00
-- url     : https://prove2.me/theorems/21f62cfd-0892-4cd9-b872-612b9fd064ec
-- title:
--   Value Aware RR: proxy Selected reversed endpoint
-- statement:
--   The Value Aware RR construction uses the proxy Selected reversed endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L321-L324
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L321-L324

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_reversed_endpoint (m : ℚ) :
    directEndpoint m (signReverse proxySelectedOrder) = 2 * (10 * m + 3) / 81 := by sorry
