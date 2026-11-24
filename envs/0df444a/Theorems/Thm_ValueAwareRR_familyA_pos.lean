-- Prove2me | Theorems.Thm_ValueAwareRR_familyA_pos
-- name    : ValueAwareRR.familyA_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:56:12.666396+00:00
-- url     : https://prove2.me/theorems/171915c3-c8e0-44c8-8c62-4ad04a9e40b3
-- title:
--   Value Aware RR: family A pos
-- statement:
--   The Value Aware RR construction uses the family A pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L566-L568
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L566-L568

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.familyA_pos (m : ℚ) (hm : 2 ≤ m) : 0 < familyA m := by sorry
