-- Prove2me | Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
-- name    : PascalExtremes.not_carryAt_iff_mod_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:49.451943+00:00
-- url     : https://prove2.me/theorems/f59ac081-ff33-5d7e-b716-decd53db0535
-- title:
--   Pascal Extremes: not carry At iff mod pow le
-- statement:
--   Absence of a carry across `p^i` is exactly prefix comparison modulo
--   `p^i`.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L40-L89
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L40-L89

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.not_carryAt_iff_mod_pow_le {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    ¬ CarryAt p n k i ↔ k % p ^ i ≤ n % p ^ i := by sorry
