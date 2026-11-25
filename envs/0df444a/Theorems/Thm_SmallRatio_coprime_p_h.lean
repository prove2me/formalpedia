-- Prove2me | Theorems.Thm_SmallRatio_coprime_p_h
-- name    : SmallRatio.coprime_p_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:48.456962+00:00
-- url     : https://prove2.me/theorems/0b115c16-44bf-5925-a1ef-0c9756ccf88d
-- title:
--   Small Ratio: coprime p h
-- statement:
--   The Small Ratio construction uses the coprime p h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L29-L29
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean#L29-L29

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp

theorem SmallRatio.coprime_p_h : Nat.Coprime p h := by sorry
