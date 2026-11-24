-- Prove2me | Theorems.Thm_Stallings_foldRel_cosetPotential
-- name    : Stallings.foldRel_cosetPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:40.463683+00:00
-- url     : https://prove2.me/theorems/10a86e5b-5564-4050-a02f-80869e0151f1
-- title:
--   Stallings: fold Rel coset Potential
-- statement:
--   A fold never identifies vertices with different subgroup cosets, whenever
--   the input graph has a compatible coset potential.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L312-L339
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L312-L339

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings

theorem Stallings.foldRel_cosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v w : V}
    (hvw : foldRel G v w) : CosetEquivalent H (potential v) (potential w) := by sorry
