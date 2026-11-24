-- Prove2me | Theorems.Thm_ValueAwareRR_normalizedLossRatio_unbounded
-- name    : ValueAwareRR.normalizedLossRatio_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:05:12.819235+00:00
-- url     : https://prove2.me/theorems/6eacb2e3-79d9-4944-9d39-1e6d58b6a2c9
-- title:
--   Value Aware RR: normalized Loss Ratio unbounded
-- statement:
--   The normalized proxy loss ratio exceeds every prescribed natural threshold.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L779-L791
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L779-L791

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedLossRatio_unbounded (N : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ (N : ℚ) ≤ normalizedLossRatio (m : ℚ) := by sorry
