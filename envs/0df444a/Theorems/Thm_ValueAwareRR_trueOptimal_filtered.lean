-- Prove2me | Theorems.Thm_ValueAwareRR_trueOptimal_filtered
-- name    : ValueAwareRR.trueOptimal_filtered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:02.624607+00:00
-- url     : https://prove2.me/theorems/c739cfca-b7c6-4279-86ab-b71640b95783
-- title:
--   Value Aware RR: true Optimal filtered
-- statement:
--   The Value Aware RR construction uses the true Optimal filtered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L273-L277
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L273-L277

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.trueOptimal_filtered (m : ℚ) : filteredSum m trueOptimalOrder = 10 / 9 := by sorry
