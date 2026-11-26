-- Prove2me | Theorems.Thm_PascalExtremes_G_ne_zero
-- name    : PascalExtremes.G_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:15.161795+00:00
-- url     : https://prove2.me/theorems/4f573831-a8b7-48ce-85a5-1244e1515b33
-- title:
--   Pascal Extremes: G ne zero
-- statement:
--   The restricted gcd is nonzero as soon as the admissible set contains `m`.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L55-L59
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L55-L59

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.G_ne_zero {N m : ℕ} (hm : 0 < m) (hNm : m < N) :
    G N m ≠ 0 := by sorry
