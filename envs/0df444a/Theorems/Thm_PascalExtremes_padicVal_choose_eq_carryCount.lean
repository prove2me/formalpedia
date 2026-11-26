-- Prove2me | Theorems.Thm_PascalExtremes_padicVal_choose_eq_carryCount
-- name    : PascalExtremes.padicVal_choose_eq_carryCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:54:54.175266+00:00
-- url     : https://prove2.me/theorems/2db291e9-eaca-44b5-88f3-4e42fcd0c791
-- title:
--   Pascal Extremes: padic Val choose eq carry Count
-- statement:
--   Thin wrapper around Mathlib's Kummer theorem `padicValNat_choose`.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L32-L36
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Kummer.lean#L32-L36

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.padicVal_choose_eq_carryCount {p n k b : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = carryCount p n k b := by sorry
