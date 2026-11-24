-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedPrefixThree_scaling
-- name    : ValueAwareRR.normalizedPrefixThree_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:40.490805+00:00
-- url     : https://prove2.me/theorems/53e85e99-f6a6-4d6f-8e6a-d4896c32a34e
-- title:
--   Value Aware RR: normalized Prefix Three scaling
-- statement:
--   The Value Aware RR construction uses the normalized Prefix Three scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L584-L588
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L584-L588

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedPrefixThree_scaling (m : ℚ) (o : SignedOrder) :
    normalizedPrefixThree m o = normalizationScale m * prefixThree m o := by sorry
