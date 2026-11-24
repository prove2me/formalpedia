-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedResidualMax_eq_one
-- name    : ValueAwareRR.normalizedResidualMax_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:03:22.045867+00:00
-- url     : https://prove2.me/theorems/3771f40f-f5ee-4eee-af7d-ef70a77f5cfa
-- title:
--   Value Aware RR: normalized Residual Max eq one
-- statement:
--   After scaling every residual by `1/(3m-1)`, the maximum magnitude is one.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L639-L643
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L639-L643

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedResidualMax_eq_one (m : ℚ) (hm : 2 ≤ m) :
    normalizedResidualMax m = 1 := by sorry
