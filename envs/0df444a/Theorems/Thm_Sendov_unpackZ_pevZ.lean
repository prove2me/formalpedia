-- Prove2me | Theorems.Thm_Sendov_unpackZ_pevZ
-- name    : Sendov.unpackZ_pevZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:24.076286+00:00
-- url     : https://prove2.me/theorems/67c5d7f9-c1ef-50c2-b3f6-75b1f3beae82
-- title:
--   Sendov: unpack Z pev Z
-- statement:
--   **Signed packing is faithful.**  If `2 * |c| < b` for every coefficient `c`, the
--   coefficients are recovered from the single integer `pevZ p b` by balanced-digit extraction.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L227-L239
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L227-L239

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.unpackZ_pevZ (b : ℤ) (hb : 0 < b) :
    ∀ p : List ℤ, (∀ a ∈ p, 2 * |a| < b) → unpackZ b p.length (pevZ p b) = p := by sorry
