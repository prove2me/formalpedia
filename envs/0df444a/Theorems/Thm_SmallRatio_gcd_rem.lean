-- Prove2me | Theorems.Thm_SmallRatio_gcd_rem
-- name    : SmallRatio.gcd_rem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:02.065468+00:00
-- url     : https://prove2.me/theorems/b242dfb5-42a9-53df-b342-8352c759bdae
-- title:
--   Small Ratio: gcd rem
-- statement:
--   The Small Ratio construction uses the gcd rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L33-L37
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L33-L37

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.gcd_rem (j : ℕ) : Nat.gcd (rem k h j) (rem k h (j + 1)) = Nat.gcd k h := by sorry
