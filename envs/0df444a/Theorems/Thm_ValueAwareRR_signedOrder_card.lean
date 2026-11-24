-- Prove2me | Theorems.Thm_ValueAwareRR_signedOrder_card
-- name    : ValueAwareRR.signedOrder_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:59:11.187637+00:00
-- url     : https://prove2.me/theorems/136a7e45-b09a-49e0-86a2-b6c4e4d7b2e1
-- title:
--   Value Aware RR: signed Order card
-- statement:
--   The encoding has exactly `4! = 24` elements.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L109-L110
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L109-L110

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.signedOrder_card : Fintype.card SignedOrder = 24 := by sorry
