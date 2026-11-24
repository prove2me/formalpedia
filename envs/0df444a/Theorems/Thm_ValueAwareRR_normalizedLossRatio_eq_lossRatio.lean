-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedLossRatio_eq_lossRatio
-- name    : ValueAwareRR.normalizedLossRatio_eq_lossRatio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T08:57:40.36937+00:00
-- url     : https://prove2.me/theorems/8b75a035-503b-44e9-8713-b3daedc7ab66
-- title:
--   Value Aware RR: normalized Loss Ratio eq loss Ratio
-- statement:
--   The Value Aware RR construction uses the normalized Loss Ratio eq loss Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L714-L722
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L714-L722

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedLossRatio_eq_lossRatio (m : ℚ) (hm : 2 ≤ m) :
    normalizedLossRatio m = lossRatio m := by sorry
