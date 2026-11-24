-- Prove2me | Theorems.Thm_ValueAwareRR_diagonalScore_signReverse
-- name    : ValueAwareRR.diagonalScore_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:54:58.047195+00:00
-- url     : https://prove2.me/theorems/98b01723-481e-4cba-8fa3-08cffe0878bf
-- title:
--   Value Aware RR: diagonal Score sign Reverse
-- statement:
--   The Value Aware RR construction uses the diagonal Score sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L226-L230
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L226-L230

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.diagonalScore_signReverse (m : ℚ) (o : SignedOrder) :
    diagonalScore m (signReverse o) = diagonalScore m o := by sorry
