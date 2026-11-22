-- Prove2me | Theorems.Thm_P2M_GridHam_chainAdjacent_append__a723f1785ceb
-- name    : P2M_GridHam_chainAdjacent_append__a723f1785ceb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:57:08.323393+00:00
-- url     : https://prove2.me/theorems/7c1d6e3d-10c2-4f2e-8b7f-27250767789f
-- title:
--   P2 M Grid Ham chain Adjacent append  a723f1785ceb: P2 M Grid Ham chain Adjacent append  a723f1785ceb
-- statement:
--   Joining two chains whose junction is adjacent (general form).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L694-L702
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L694-L702

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_chainAdjacent_append__a723f1785ceb (l1 M : List Coord) (a b : Coord) (hl : l1.getLast? = some a)
    (h1 : chainAdjacent l1 = true) (hM : M.head? = some b) (hadj : Adjacent a b)
    (h2 : chainAdjacent M = true) : chainAdjacent (l1 ++ M) = true := by sorry

alias «GridHam».«chainAdjacent_append'» := P2M_GridHam_chainAdjacent_append__a723f1785ceb
