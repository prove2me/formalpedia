-- Prove2me | Theorems.Thm_Stallings_CosetEquivalent_mem_of_mem_and_rel
-- name    : Stallings.CosetEquivalent.mem_of_mem_and_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:47.175314+00:00
-- url     : https://prove2.me/theorems/d57d0bee-4197-4b51-8393-317986504642
-- title:
--   Coset Equivalent: mem of mem and rel
-- statement:
--   The Coset Equivalent construction uses the mem of mem and rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L261-L267
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L261-L267

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings
open Stallings.CosetEquivalent

theorem Stallings.CosetEquivalent.mem_of_mem_and_rel {H : Subgroup Free} {g h : Free}
    (hgh : CosetEquivalent H g h) (hg : g ∈ H) : h ∈ H := by sorry
