-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_reversed_loss
-- name    : ValueAwareRR.proxySelected_reversed_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:09:24.270735+00:00
-- url     : https://prove2.me/theorems/a1208bed-f162-45b3-9674-81665a22e918
-- title:
--   Value Aware RR: proxy Selected reversed loss
-- statement:
--   The Value Aware RR construction uses the proxy Selected reversed loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L330-L333
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L330-L333

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_reversed_loss (m : ℚ) :
    exactLoss m (signReverse proxySelectedOrder) =
      2 * (10 * m + 3) ^ 2 / 6561 := by sorry
