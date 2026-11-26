-- Prove2me | Theorems.Thm_PascalExtremes_carryAt_iff_mod_pow_lt
-- name    : PascalExtremes.carryAt_iff_mod_pow_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:56.584109+00:00
-- url     : https://prove2.me/theorems/6be8e7cd-1d5a-58b3-84a2-bc7c360983c7
-- title:
--   Pascal Extremes: carry At iff mod pow lt
-- statement:
--   Residue/borrow form of Kummer's carry predicate.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L92-L96
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L92-L96

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.carryAt_iff_mod_pow_lt {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    CarryAt p n k i ↔ n % p ^ i < k % p ^ i := by sorry
