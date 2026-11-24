-- Prove2me | Theorems.Thm_ValueAwareRR_diagonalScore_minimizer_iff
-- name    : ValueAwareRR.diagonalScore_minimizer_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:01:52.789017+00:00
-- url     : https://prove2.me/theorems/8497b5d9-a466-458e-ba6e-aebe3b3dc9ce
-- title:
--   Value Aware RR: diagonal Score minimizer iff
-- statement:
--   The diagonal-in-time proxy has exactly the same two minimizers.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L478-L504
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L478-L504

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.diagonalScore_minimizer_iff (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    diagonalScore m o = diagonalScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by sorry
