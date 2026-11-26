-- Prove2me | Theorems.Thm_RamseyLib_four_mul_two_pow_lt_factorial_sq
-- name    : RamseyLib.four_mul_two_pow_lt_factorial_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:50.782982+00:00
-- url     : https://prove2.me/theorems/71956861-a43b-4dd5-9a91-c5d06ca6ee83
-- title:
--   Ramsey Lib: four mul two pow lt factorial sq
-- statement:
--   The Ramsey Lib construction uses the four mul two pow lt factorial sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L136-L142
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L136-L142

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.four_mul_two_pow_lt_factorial_sq (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by sorry
