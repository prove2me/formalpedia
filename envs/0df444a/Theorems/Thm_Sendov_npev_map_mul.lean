-- Prove2me | Theorems.Thm_Sendov_npev_map_mul
-- name    : Sendov.npev_map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:49.222799+00:00
-- url     : https://prove2.me/theorems/758238a9-264f-472e-8d18-4ff3514c49eb
-- title:
--   Sendov: npev map mul
-- statement:
--   The Sendov construction uses the npev map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L121-L127
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean#L121-L127

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
set_option autoImplicit false
open Sendov

theorem Sendov.npev_map_mul (a : ℕ) (q : List ℕ) (b : ℕ) :
    npev (q.map (fun c => a * c)) b = a * npev q b := by sorry
