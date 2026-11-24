-- Prove2me | Theorems.Thm_Stallings_foldWalk
-- name    : Stallings.foldWalk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:45.299734+00:00
-- url     : https://prove2.me/theorems/fbbeb0a3-8937-4e81-b457-998752de445e
-- title:
--   Stallings: fold Walk
-- statement:
--   Folding preserves every path in the original multigraph, after mapping its
--   endpoints to their canonical representatives.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L226-L236
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L226-L236

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.foldWalk {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (base v z : V)
    {w : Word} (h : G.Walk v w z) :
    (foldAutomaton G base).run (foldRep G v) w = some (foldRep G z) := by sorry
