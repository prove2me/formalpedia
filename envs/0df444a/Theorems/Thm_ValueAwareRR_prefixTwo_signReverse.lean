-- Prove2me | Theorems.Thm_ValueAwareRR_prefixTwo_signReverse
-- name    : ValueAwareRR.prefixTwo_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:22.955404+00:00
-- url     : https://prove2.me/theorems/f7363ea4-ff2b-43fa-a147-ae0f8bead52c
-- title:
--   Value Aware RR: prefix Two sign Reverse
-- statement:
--   The Value Aware RR construction uses the prefix Two sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L199-L202
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L199-L202

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.prefixTwo_signReverse (m : ℚ) (o : SignedOrder) :
    prefixTwo m (signReverse o) = -prefixTwo m o := by sorry
