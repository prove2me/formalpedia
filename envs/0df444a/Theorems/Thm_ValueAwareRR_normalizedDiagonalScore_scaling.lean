-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedDiagonalScore_scaling
-- name    : ValueAwareRR.normalizedDiagonalScore_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:57:38.867895+00:00
-- url     : https://prove2.me/theorems/a63be15b-e509-47e7-8443-3141b4380a19
-- title:
--   Value Aware RR: normalized Diagonal Score scaling
-- statement:
--   The Value Aware RR construction uses the normalized Diagonal Score scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L602-L606
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L602-L606

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedDiagonalScore_scaling (m : ℚ) (o : SignedOrder) :
    normalizedDiagonalScore m o = normalizationScale m ^ 2 * diagonalScore m o := by sorry
