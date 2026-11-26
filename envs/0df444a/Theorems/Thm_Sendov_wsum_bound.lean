-- Prove2me | Theorems.Thm_Sendov_wsum_bound
-- name    : Sendov.wsum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:27.646266+00:00
-- url     : https://prove2.me/theorems/bdd5400f-67b3-5072-972d-ff08f3ef63a1
-- title:
--   Sendov: wsum bound
-- statement:
--   The `β` bound for the moment numerator.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L568-L576
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L568-L576

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.wsum_bound (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β : ℤ) (hL : 0 ≤ L)
    (hβ : 2 * (L * (l1 g₀ + l1 g₁ + l1 g₂) ^ k) < β) :
    ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β := by sorry
