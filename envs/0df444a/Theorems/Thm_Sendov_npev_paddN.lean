-- Prove2me | Theorems.Thm_Sendov_npev_paddN
-- name    : Sendov.npev_paddN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:47.474656+00:00
-- url     : https://prove2.me/theorems/b2d89ba1-47fd-5dbd-9c54-ad5b965ed2ad
-- title:
--   Sendov: npev padd N
-- statement:
--   The Sendov construction uses the npev padd N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L110-L119
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L110-L119

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.npev_paddN (p q : List ℕ) (b : ℕ) :
    npev (paddN p q) b = npev p b + npev q b := by sorry
