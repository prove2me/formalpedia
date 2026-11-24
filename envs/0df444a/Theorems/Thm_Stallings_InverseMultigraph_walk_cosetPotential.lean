-- Prove2me | Theorems.Thm_Stallings_InverseMultigraph_walk_cosetPotential
-- name    : Stallings.InverseMultigraph.walk_cosetPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:49.701799+00:00
-- url     : https://prove2.me/theorems/a8a96bf5-f38c-4a46-9324-bfeec8dc8fdb
-- title:
--   Inverse Multigraph: walk coset Potential
-- statement:
--   Along any path, a coset potential changes by the value of the path label.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L285-L298
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L285-L298

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.InverseMultigraph.walk_cosetPotential {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V] (G : InverseMultigraph V) (H : Subgroup Free)
    (potential : V → Free) (hpotential : HasCosetPotential G H potential) :
    ∀ {v z : V} {w : Word}, G.Walk v w z →
      CosetEquivalent H (potential z) (potential v * wordEval w) := by sorry
