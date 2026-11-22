-- Prove2me | Theorems.Thm_P2M_GridHam_mem_of_getLast__beac85f634f6
-- name    : P2M_GridHam_mem_of_getLast__beac85f634f6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:39:53.795238+00:00
-- url     : https://prove2.me/theorems/c45c6107-cf06-41ec-a70c-afb49c3966ac
-- title:
--   P2 M Grid Ham mem of get Last  beac85f634f6: P2 M Grid Ham mem of get Last  beac85f634f6
-- statement:
--   The P2 M Grid Ham mem of get Last  beac85f634f6 construction uses the P2 M Grid Ham mem of get Last  beac85f634f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L981-L995
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L981-L995

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_mem_of_getLast__beac85f634f6 : ∀ (l : List Coord) (t : Coord), l.getLast? = some t → t ∈ l := by sorry

alias «GridHam».«mem_of_getLast?» := P2M_GridHam_mem_of_getLast__beac85f634f6
