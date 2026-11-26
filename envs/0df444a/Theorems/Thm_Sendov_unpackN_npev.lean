-- Prove2me | Theorems.Thm_Sendov_unpackN_npev
-- name    : Sendov.unpackN_npev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:16.828015+00:00
-- url     : https://prove2.me/theorems/006691b8-d30a-5351-9295-bdfc2a838993
-- title:
--   Sendov: unpack N npev
-- statement:
--   **Packing is faithful.**  If every coefficient is smaller than the base, evaluation at
--   the base loses nothing: the coefficients can be read back off by division with remainder.
--
--   This is the standard Kronecker-substitution correctness statement, and the hypothesis
--   `∀ a ∈ p, a < b` is exactly the overflow condition the caller must discharge.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L67-L80
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L67-L80

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.unpackN_npev (b : ℕ) (hb : 0 < b) :
    ∀ p : List ℕ, (∀ a ∈ p, a < b) → unpackN b p.length (npev p b) = p := by sorry
