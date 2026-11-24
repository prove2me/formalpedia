-- Prove2me | Theorems.Thm_ValueAwareRR_filteredSum_signReverse
-- name    : ValueAwareRR.filteredSum_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:07.205836+00:00
-- url     : https://prove2.me/theorems/fe9ed2fc-b0fc-4e2f-9210-bf52deb52c66
-- title:
--   Value Aware RR: filtered Sum sign Reverse
-- statement:
--   The Value Aware RR construction uses the filtered Sum sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L209-L213
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L209-L213

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.filteredSum_signReverse (m : ℚ) (o : SignedOrder) :
    filteredSum m (signReverse o) = -filteredSum m o := by sorry
