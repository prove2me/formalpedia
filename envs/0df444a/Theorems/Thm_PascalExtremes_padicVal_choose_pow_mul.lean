-- Prove2me | Theorems.Thm_PascalExtremes_padicVal_choose_pow_mul
-- name    : PascalExtremes.padicVal_choose_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:56:21.76549+00:00
-- url     : https://prove2.me/theorems/daf187fe-c044-460e-a548-d860384b02f2
-- title:
--   Pascal Extremes: padic Val choose pow mul
-- statement:
--   Multiplying both entries of a binomial coefficient by the same power of
--   `p` preserves its `p`-adic valuation.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Scaling.lean#L29-L42
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Scaling.lean#L29-L42

module
public import Definitions.Def_PascalExtremes_Basic
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Scaling
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.padicVal_choose_pow_mul
    {p c n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    padicValNat p ((p ^ c * n).choose (p ^ c * k)) =
      padicValNat p (n.choose k) := by sorry
