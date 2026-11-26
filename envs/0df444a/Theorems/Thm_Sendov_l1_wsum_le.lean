-- Prove2me | Theorems.Thm_Sendov_l1_wsum_le
-- name    : Sendov.l1_wsum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:21.936379+00:00
-- url     : https://prove2.me/theorems/0952bc15-6bfc-5f00-971f-3f3a6ea725f7
-- title:
--   Sendov: l1 wsum le
-- statement:
--   The weighted sum's `L¹` norm is at most `L` times the row's.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L521-L537
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L521-L537

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_wsum_le (L : ℤ) (hL : 0 ≤ L) : ∀ (r : List (List ℤ)) (i : ℕ),
    l1 (wsum L i r) ≤ L * l1row r := by sorry
