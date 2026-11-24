-- Prove2me | Theorems.Thm_ValueAwareRR_lossRatio_lower_bound
-- name    : ValueAwareRR.lossRatio_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:00:22.393513+00:00
-- url     : https://prove2.me/theorems/d9c34cc8-4b0a-4dda-bbcf-2344d275294d
-- title:
--   Value Aware RR: loss Ratio lower bound
-- statement:
--   The Value Aware RR construction uses the loss Ratio lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L343-L346
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L343-L346

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.lossRatio_lower_bound (m : ℚ) (hm : 0 ≤ m) :
    4 * m ^ 2 ≤ lossRatio m := by sorry
