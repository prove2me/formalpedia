-- Prove2me | Theorems.Thm_Stallings_CosetEquivalent_trans
-- name    : Stallings.CosetEquivalent.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:37.462013+00:00
-- url     : https://prove2.me/theorems/f27c3a6b-3d1f-4d54-90b5-33c80a5df6a2
-- title:
--   Coset Equivalent: trans
-- statement:
--   The Coset Equivalent construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L252-L259
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L252-L259

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings
open Stallings.CosetEquivalent

theorem Stallings.CosetEquivalent.trans {H : Subgroup Free} {g h k : Free}
    (gh : CosetEquivalent H g h) (hk : CosetEquivalent H h k) :
    CosetEquivalent H g k := by sorry
