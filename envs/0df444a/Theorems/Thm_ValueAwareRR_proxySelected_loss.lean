-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelected_loss
-- name    : ValueAwareRR.proxySelected_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:55:55.48545+00:00
-- url     : https://prove2.me/theorems/9b0c0433-b90d-473b-8878-cb4fd53755d4
-- title:
--   Value Aware RR: proxy Selected loss
-- statement:
--   The Value Aware RR construction uses the proxy Selected loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L290-L294
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L290-L294

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelected_loss (m : ℚ) :
    exactLoss m proxySelectedOrder = 2 * (10 * m + 3) ^ 2 / 6561 := by sorry
