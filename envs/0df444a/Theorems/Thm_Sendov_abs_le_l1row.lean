-- Prove2me | Theorems.Thm_Sendov_abs_le_l1row
-- name    : Sendov.abs_le_l1row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:12:24.705435+00:00
-- url     : https://prove2.me/theorems/287a1838-942e-5eeb-a283-bd74f7c759f8
-- title:
--   Sendov: abs le l1row
-- statement:
--   Every coefficient of every entry of a row is bounded by the row's `L¹` norm.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L622-L637
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L622-L637

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.abs_le_l1row : ∀ (r : List (List ℤ)) (p : List ℤ), p ∈ r → ∀ a ∈ p, |a| ≤ l1row r := by sorry
