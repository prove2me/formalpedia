-- Prove2me | Theorems.Thm_ValueAwareRR_maxPrefixScore_table
-- name    : ValueAwareRR.maxPrefixScore_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:30.435463+00:00
-- url     : https://prove2.me/theorems/a0d2ea39-d1e1-4b58-9550-9b85e3174bc0
-- title:
--   Value Aware RR: max Prefix Score table
-- statement:
--   The Value Aware RR construction uses the max Prefix Score table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L399-L410
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L399-L410

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.maxPrefixScore_table (m : ℚ) (hm : 2 ≤ m) (r : Representative) :
    maxPrefixScore m (r, false) = maxPrefixTable m r := by sorry
