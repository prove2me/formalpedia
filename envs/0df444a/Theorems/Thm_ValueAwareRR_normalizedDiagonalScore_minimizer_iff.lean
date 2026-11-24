-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedDiagonalScore_minimizer_iff
-- name    : ValueAwareRR.normalizedDiagonalScore_minimizer_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:04:07.741895+00:00
-- url     : https://prove2.me/theorems/96a9e7c5-4349-4ab5-93ae-d100ffd81379
-- title:
--   Value Aware RR: normalized Diagonal Score minimizer iff
-- statement:
--   Positive common normalization preserves the diagonal-score argmin set.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L675-L686
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L675-L686

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedDiagonalScore_minimizer_iff
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedDiagonalScore m o = normalizedDiagonalScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by sorry
