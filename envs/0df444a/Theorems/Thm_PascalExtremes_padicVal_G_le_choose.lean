-- Prove2me | Theorems.Thm_PascalExtremes_padicVal_G_le_choose
-- name    : PascalExtremes.padicVal_G_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:24.040656+00:00
-- url     : https://prove2.me/theorems/a594469f-ab7e-4f53-9f1c-23809503b2be
-- title:
--   Pascal Extremes: padic Val G le choose
-- statement:
--   The valuation of the restricted gcd is bounded by that of every selected coefficient.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L63-L84
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean#L63-L84

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.padicVal_G_le_choose
    {N m p k : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hk : Admissible N m k) :
    padicValNat p (G N m) ≤ padicValNat p (N.choose k) := by sorry
