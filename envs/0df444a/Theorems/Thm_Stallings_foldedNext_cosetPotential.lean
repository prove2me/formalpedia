-- Prove2me | Theorems.Thm_Stallings_foldedNext_cosetPotential
-- name    : Stallings.foldedNext_cosetPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:47.62389+00:00
-- url     : https://prove2.me/theorems/aab80446-db0b-4d9b-86c5-ea7e128c3026
-- title:
--   Stallings: folded Next coset Potential
-- statement:
--   Each transition made by the folded automaton respects the subgroup
--   potential.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L343-L377
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L343-L377

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.foldedNext_cosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (base : V) (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v t : V} {x : Letter}
    (hnext : (foldAutomaton G base).next v x = some t) :
    CosetEquivalent H (potential t) (potential v * letterEval x) := by sorry
