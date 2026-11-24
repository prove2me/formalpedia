-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedProxy_diagonal_global_minimum
-- name    : ValueAwareRR.normalizedProxy_diagonal_global_minimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:04:53.812394+00:00
-- url     : https://prove2.me/theorems/7f2ced64-062d-44c2-a309-262dff23c8af
-- title:
--   Value Aware RR: normalized Proxy diagonal global minimum
-- statement:
--   The Value Aware RR construction uses the normalized Proxy diagonal global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L703-L708
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L703-L708

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedProxy_diagonal_global_minimum
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedDiagonalScore m proxySelectedOrder ≤ normalizedDiagonalScore m o := by sorry
