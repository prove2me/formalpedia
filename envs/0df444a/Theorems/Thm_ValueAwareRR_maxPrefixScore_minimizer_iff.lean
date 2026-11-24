-- Prove2me | Theorems.Thm_ValueAwareRR_maxPrefixScore_minimizer_iff
-- name    : ValueAwareRR.maxPrefixScore_minimizer_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:01:33.166439+00:00
-- url     : https://prove2.me/theorems/80dc5c7e-ab28-4405-8c2e-3f16c39066bb
-- title:
--   Value Aware RR: max Prefix Score minimizer iff
-- statement:
--   The maximum-prefix proxy has exactly the two claimed minimizers.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L439-L462
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L439-L462

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.maxPrefixScore_minimizer_iff (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    maxPrefixScore m o = maxPrefixScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by sorry
