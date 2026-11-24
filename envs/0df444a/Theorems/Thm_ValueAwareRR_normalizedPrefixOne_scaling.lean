-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedPrefixOne_scaling
-- name    : ValueAwareRR.normalizedPrefixOne_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:51.940904+00:00
-- url     : https://prove2.me/theorems/6e9e2a8c-6ba9-4b13-a920-3f0bce1d4f2b
-- title:
--   Value Aware RR: normalized Prefix One scaling
-- statement:
--   The Value Aware RR construction uses the normalized Prefix One scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L574-L576
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L574-L576

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedPrefixOne_scaling (m : ℚ) (o : SignedOrder) :
    normalizedPrefixOne m o = normalizationScale m * prefixOne m o := by sorry
