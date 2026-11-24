-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedPrefixTwo_scaling
-- name    : ValueAwareRR.normalizedPrefixTwo_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:45.87113+00:00
-- url     : https://prove2.me/theorems/be44c8f5-23cb-4425-b209-1cf144e593bf
-- title:
--   Value Aware RR: normalized Prefix Two scaling
-- statement:
--   The Value Aware RR construction uses the normalized Prefix Two scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L578-L582
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L578-L582

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedPrefixTwo_scaling (m : ℚ) (o : SignedOrder) :
    normalizedPrefixTwo m o = normalizationScale m * prefixTwo m o := by sorry
