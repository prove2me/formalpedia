-- Prove2me | Theorems.Thm_Stallings_flowerGraph_loopSubgroup_eq_generatorSubgroup
-- name    : Stallings.flowerGraph_loopSubgroup_eq_generatorSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:13:55.321706+00:00
-- url     : https://prove2.me/theorems/8c3cd135-3d8f-4357-868a-440c18f8a636
-- title:
--   Stallings: flower Graph loop Subgroup eq generator Subgroup
-- statement:
--   The loop subgroup of the initial flower is exactly the subgroup generated
--   by the input words.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Flower.lean#L289-L310
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Flower.lean#L289-L310

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
set_option autoImplicit true
open Stallings

theorem Stallings.flowerGraph_loopSubgroup_eq_generatorSubgroup (S : List Word) :
    (flowerGraph S).loopSubgroup none = generatorSubgroup S := by sorry
