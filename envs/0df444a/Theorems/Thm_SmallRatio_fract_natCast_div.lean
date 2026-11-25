-- Prove2me | Theorems.Thm_SmallRatio_fract_natCast_div
-- name    : SmallRatio.fract_natCast_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:04.607485+00:00
-- url     : https://prove2.me/theorems/61364d4f-aeb2-4e58-bba8-c45582f4b0fa
-- title:
--   Small Ratio: fract nat Cast div
-- statement:
--   The Small Ratio construction uses the fract nat Cast div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L25-L39
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L25-L39

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.fract_natCast_div (n k : ℕ) (hk : 0 < k) :
    Int.fract ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k := by sorry
