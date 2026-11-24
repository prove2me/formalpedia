-- Prove2me | Theorems.Thm_ValueAwareRR_normalizationScale_pos
-- name    : ValueAwareRR.normalizationScale_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:08.743281+00:00
-- url     : https://prove2.me/theorems/9aa61ba4-fa61-4528-bf50-b82c5132ed27
-- title:
--   Value Aware RR: normalization Scale pos
-- statement:
--   The Value Aware RR construction uses the normalization Scale pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L570-L572
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L570-L572

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizationScale_pos (m : ℚ) (hm : 2 ≤ m) : 0 < normalizationScale m := by sorry
