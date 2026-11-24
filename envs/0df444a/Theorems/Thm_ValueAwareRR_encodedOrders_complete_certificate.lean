-- Prove2me | Theorems.Thm_ValueAwareRR_encodedOrders_complete_certificate
-- name    : ValueAwareRR.encodedOrders_complete_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:59:19.00814+00:00
-- url     : https://prove2.me/theorems/724ca1b5-07de-46ff-9ae6-21cd9860d49c
-- title:
--   Value Aware RR: encoded Orders complete certificate
-- statement:
--   The two facts above are the finite completeness certificate for the encoding.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L117-L120
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L117-L120

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.encodedOrders_complete_certificate :
    Function.Injective encodedPermutation ∧
      Fintype.card SignedOrder = Fintype.card (Equiv.Perm (Fin 4)) := by sorry
