-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_filtered
-- name    : ValueAwareRR.proxySelected_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:07.97073+00:00
-- url     : https://prove2.me/theorems/1a8c177c-7011-496a-bd89-844cfc3707db
-- title:
--   Value Aware RR: proxy Selected filtered
-- statement:
--   The Value Aware RR construction uses the proxy Selected filtered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L279-L284
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L279-L284

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_filtered (m : ℚ) :
    filteredSum m proxySelectedOrder = -2 * (10 * m + 3) / 9 := by sorry
