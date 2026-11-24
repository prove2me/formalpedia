-- Prove2me | Theorems.Thm_ValueAwareRR_diagonalScore_margin_table
-- name    : ValueAwareRR.diagonalScore_margin_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:56:16.378121+00:00
-- url     : https://prove2.me/theorems/ccb15afb-3017-462d-9aed-460a98738c10
-- title:
--   Value Aware RR: diagonal Score margin table
-- statement:
--   The Value Aware RR construction uses the diagonal Score margin table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L391-L397
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L391-L397

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.diagonalScore_margin_table (m : ℚ) (r : Representative) :
    81 * (diagonalScore m (r, false) -
      diagonalScore m proxySelectedOrder) = diagonalMarginTable m r := by sorry
