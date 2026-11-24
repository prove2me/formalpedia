-- Prove2me | Theorems.Thm_Stallings_run_cosetPotential
-- name    : Stallings.run_cosetPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:13:35.331242+00:00
-- url     : https://prove2.me/theorems/cbee36c6-ffbb-4c31-b3f1-e4fe2b474704
-- title:
--   Stallings: run coset Potential
-- statement:
--   A successful folded traversal transports the potential by the value of its
--   label word.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L381-L404
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L381-L404

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.run_cosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (base : V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) :
    ∀ {v t : V} {w : Word},
      (foldAutomaton G base).run v w = some t →
      CosetEquivalent H (potential t) (potential v * wordEval w) := by sorry
