-- Prove2me | Theorems.Thm_Sendov_qrow_length
-- name    : Sendov.qrow_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:24.81326+00:00
-- url     : https://prove2.me/theorems/7088d803-17ec-590c-be6d-acb58aa7bce9
-- title:
--   Sendov: qrow length
-- statement:
--   The row of the `k`-th power has `2k+1` entries, whatever the multiplier.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L282-L288
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L282-L288

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.qrow_length (g₀ g₁ g₂ : List ℤ) (k : ℕ) :
    (qrow g₀ g₁ g₂ k).length = 2 * k + 1 := by sorry
