-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedExactLoss_scaling
-- name    : ValueAwareRR.normalizedExactLoss_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:08.797277+00:00
-- url     : https://prove2.me/theorems/a5d83f01-063f-43ae-ac06-acfc3211ce2d
-- title:
--   Value Aware RR: normalized Exact Loss scaling
-- statement:
--   The Value Aware RR construction uses the normalized Exact Loss scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L596-L600
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L596-L600

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedExactLoss_scaling (m : ℚ) (o : SignedOrder) :
    normalizedExactLoss m o = normalizationScale m ^ 2 * exactLoss m o := by sorry
