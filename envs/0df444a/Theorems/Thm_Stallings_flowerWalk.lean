-- Prove2me | Theorems.Thm_Stallings_flowerWalk
-- name    : Stallings.flowerWalk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:13:58.173523+00:00
-- url     : https://prove2.me/theorems/2f9cea80-2d38-461d-a54b-849b374910a9
-- title:
--   Stallings: flower Walk
-- statement:
--   Each input word labels a closed path in the flower graph.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Flower.lean#L282-L285
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Flower.lean#L282-L285

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

theorem Stallings.flowerWalk (S : List Word) (i : Fin S.length) :
    (flowerGraph S).Walk none (S.get i) none := by sorry
