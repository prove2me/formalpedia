-- Prove2me | Theorems.Thm_Sendov_unpackZ_succ
-- name    : Sendov.unpackZ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:14.300695+00:00
-- url     : https://prove2.me/theorems/f87a2555-934f-5c99-bd6b-a37f8c39bdca
-- title:
--   Sendov: unpack Z succ
-- statement:
--   The Sendov construction uses the unpack Z succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L201-L202
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L201-L202

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.unpackZ_succ (b : ℤ) (m : ℕ) (x : ℤ) :
    unpackZ b (m + 1) x = bdig b x :: unpackZ b m ((x - bdig b x) / b) := by sorry

attribute [defeq] Sendov.unpackZ_succ
