-- Prove2me | Theorems.Thm_Stallings_foldedNext_of_edge
-- name    : Stallings.foldedNext_of_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:42.047532+00:00
-- url     : https://prove2.me/theorems/747b56b0-663c-4de2-8ea5-7c038d5e30f9
-- title:
--   Stallings: folded Next of edge
-- statement:
--   Every original edge induces the corresponding transition between fold
--   representatives.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L204-L222
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L204-L222

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.foldedNext_of_edge {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) {v t : V}
    {x : Letter} (hedge : t ∈ G.edges v x) :
    foldedNext G (foldRep G v) x = some (foldRep G t) := by sorry
