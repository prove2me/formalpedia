-- Prove2me | Theorems.Thm_P2M_GridHam_nodup_append_right__a582c6ad4e63
-- name    : P2M_GridHam_nodup_append_right__a582c6ad4e63
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:47:07.49771+00:00
-- url     : https://prove2.me/theorems/2570c2bf-411e-4e05-8bed-d90d46965d3f
-- title:
--   P2 M Grid Ham nodup append right  a582c6ad4e63: P2 M Grid Ham nodup append right  a582c6ad4e63
-- statement:
--   The P2 M Grid Ham nodup append right  a582c6ad4e63 construction uses the P2 M Grid Ham nodup append right  a582c6ad4e63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L245-L252
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L245-L252

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_nodup_append_right__a582c6ad4e63 : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup → l2.Nodup := by sorry

alias «GridHam».«nodup_append_right'» := P2M_GridHam_nodup_append_right__a582c6ad4e63
