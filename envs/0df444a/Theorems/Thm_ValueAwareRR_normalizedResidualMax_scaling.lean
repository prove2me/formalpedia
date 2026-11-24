-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedResidualMax_scaling
-- name    : ValueAwareRR.normalizedResidualMax_scaling
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:03:07.918803+00:00
-- url     : https://prove2.me/theorems/4ee6f817-55d4-4305-8196-3b747623a565
-- title:
--   Value Aware RR: normalized Residual Max scaling
-- statement:
--   The Value Aware RR construction uses the normalized Residual Max scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L625-L636
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L625-L636

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedResidualMax_scaling (m : ℚ) (hm : 2 ≤ m) :
    normalizedResidualMax m = normalizationScale m * residualMax m := by sorry
