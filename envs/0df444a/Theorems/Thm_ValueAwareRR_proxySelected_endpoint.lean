-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_endpoint
-- name    : ValueAwareRR.proxySelected_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:08:28.074067+00:00
-- url     : https://prove2.me/theorems/ce9b830b-faa4-43c1-be4b-1161e40f86c7
-- title:
--   Value Aware RR: proxy Selected endpoint
-- statement:
--   The Value Aware RR construction uses the proxy Selected endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L301-L304
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L301-L304

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_endpoint (m : ℚ) :
    directEndpoint m proxySelectedOrder = -2 * (10 * m + 3) / 81 := by sorry
