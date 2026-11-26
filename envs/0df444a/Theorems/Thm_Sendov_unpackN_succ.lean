-- Prove2me | Theorems.Thm_Sendov_unpackN_succ
-- name    : Sendov.unpackN_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:11.748639+00:00
-- url     : https://prove2.me/theorems/3ab03691-bad1-4cd9-8bc0-a62c618531dc
-- title:
--   Sendov: unpack N succ
-- statement:
--   The Sendov construction uses the unpack N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L59-L60
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L59-L60

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.unpackN_succ (b m x : ℕ) :
    unpackN b (m + 1) x = (x % b) :: unpackN b m (x / b) := by sorry

attribute [defeq] Sendov.unpackN_succ
