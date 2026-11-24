-- Prove2me | Theorems.Thm_ValueAwareRR_representativeOrder_injective
-- name    : ValueAwareRR.representativeOrder_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:58:19.232822+00:00
-- url     : https://prove2.me/theorems/3773f469-2d4f-45f1-b136-29f057eecb23
-- title:
--   Value Aware RR: representative Order injective
-- statement:
--   The Value Aware RR construction uses the representative Order injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L58-L64
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L58-L64

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.representativeOrder_injective : Function.Injective representativeOrder := by sorry
