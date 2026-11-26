-- Prove2me | Theorems.Thm_Sendov_pevZ_inj
-- name    : Sendov.pevZ_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:03.987791+00:00
-- url     : https://prove2.me/theorems/379f59e7-6b48-59d2-9a91-9c06cc7b3ef8
-- title:
--   Sendov: pev Z inj
-- statement:
--   Packing is injective on lists of the same length with coefficients below `β/2`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L396-L401
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L396-L401

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pevZ_inj (β : ℤ) (hβ : 0 < β) (p q : List ℤ)
    (hp : ∀ a ∈ p, 2 * |a| < β) (hq : ∀ a ∈ q, 2 * |a| < β)
    (hlen : p.length = q.length) (h : pevZ p β = pevZ q β) : p = q := by sorry
