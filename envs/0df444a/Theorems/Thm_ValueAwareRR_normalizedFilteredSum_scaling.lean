-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedFilteredSum_scaling
-- name    : ValueAwareRR.normalizedFilteredSum_scaling
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:02:39.404099+00:00
-- url     : https://prove2.me/theorems/5e0d9c6c-a094-4dd8-88b0-4544542c9ace
-- title:
--   Value Aware RR: normalized Filtered Sum scaling
-- statement:
--   The Value Aware RR construction uses the normalized Filtered Sum scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L590-L594
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L590-L594

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedFilteredSum_scaling (m : ℚ) (o : SignedOrder) :
    normalizedFilteredSum m o = normalizationScale m * filteredSum m o := by sorry
