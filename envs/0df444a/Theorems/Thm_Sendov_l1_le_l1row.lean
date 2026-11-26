-- Prove2me | Theorems.Thm_Sendov_l1_le_l1row
-- name    : Sendov.l1_le_l1row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:18.244351+00:00
-- url     : https://prove2.me/theorems/a4df97f3-6c1c-524b-8bc2-5d9c31bde7eb
-- title:
--   Sendov: l1 le l1row
-- statement:
--   `l1` of an entry is at most `l1row` of the row.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L497-L505
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L497-L505

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_le_l1row : ∀ (r : List (List ℤ)) (p : List ℤ), p ∈ r → l1 p ≤ l1row r := by sorry
