-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedMaxPrefixScore_scaling
-- name    : ValueAwareRR.normalizedMaxPrefixScore_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:57:19.894892+00:00
-- url     : https://prove2.me/theorems/98395ce7-c1fa-4b38-8a87-bb7b21972f62
-- title:
--   Value Aware RR: normalized Max Prefix Score scaling
-- statement:
--   The Value Aware RR construction uses the normalized Max Prefix Score scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L608-L615
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L608-L615

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedMaxPrefixScore_scaling
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m o = normalizationScale m * maxPrefixScore m o := by sorry
