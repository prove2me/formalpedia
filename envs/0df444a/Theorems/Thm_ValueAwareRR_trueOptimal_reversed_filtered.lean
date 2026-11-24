-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_reversed_filtered
-- name    : ValueAwareRR.trueOptimal_reversed_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:00:17.55464+00:00
-- url     : https://prove2.me/theorems/a0933a61-86c6-4dee-8517-893e736fae70
-- title:
--   Value Aware RR: true Optimal reversed filtered
-- statement:
--   The Value Aware RR construction uses the true Optimal reversed filtered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L306-L309
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L306-L309

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_reversed_filtered (m : ℚ) :
    filteredSum m (signReverse trueOptimalOrder) = -10 / 9 := by sorry
