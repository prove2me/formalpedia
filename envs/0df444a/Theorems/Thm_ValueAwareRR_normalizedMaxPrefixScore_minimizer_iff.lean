-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedMaxPrefixScore_minimizer_iff
-- name    : ValueAwareRR.normalizedMaxPrefixScore_minimizer_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:03:41.867459+00:00
-- url     : https://prove2.me/theorems/fb5692a7-4568-4f0e-84f3-acf6bedc2a0b
-- title:
--   Value Aware RR: normalized Max Prefix Score minimizer iff
-- statement:
--   Positive common normalization preserves the maximum-prefix argmin set.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L660-L672
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L660-L672

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedMaxPrefixScore_minimizer_iff
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m o = normalizedMaxPrefixScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by sorry
