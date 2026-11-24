-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_reversed_filtered
-- name    : ValueAwareRR.proxySelected_reversed_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:00:38.707817+00:00
-- url     : https://prove2.me/theorems/dad3be48-685b-440a-b1f4-e6391aa9f56d
-- title:
--   Value Aware RR: proxy Selected reversed filtered
-- statement:
--   The Value Aware RR construction uses the proxy Selected reversed filtered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L311-L314
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L311-L314

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_reversed_filtered (m : ℚ) :
    filteredSum m (signReverse proxySelectedOrder) = 2 * (10 * m + 3) / 9 := by sorry
