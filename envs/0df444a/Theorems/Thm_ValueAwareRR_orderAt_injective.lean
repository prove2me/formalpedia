-- Prove2me | Theorems.Thm_ValueAwareRR_orderAt_injective
-- name    : ValueAwareRR.orderAt_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:58:55.383572+00:00
-- url     : https://prove2.me/theorems/83ee8e03-886e-4169-be64-ea3c1527cd68
-- title:
--   Value Aware RR: order At injective
-- statement:
--   The Value Aware RR construction uses the order At injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L78-L100
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L78-L100

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.orderAt_injective : Function.Injective orderAt := by sorry
