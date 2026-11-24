-- Prove2me | Theorems.Thm_Stallings_CosetEquivalent_right_mul
-- name    : Stallings.CosetEquivalent.right_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:12:34.375342+00:00
-- url     : https://prove2.me/theorems/016901ce-5eba-4940-a108-7b1d85bedbaa
-- title:
--   Coset Equivalent: right mul
-- statement:
--   The Coset Equivalent construction uses the right mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L269-L273
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean#L269-L273

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding
set_option autoImplicit true
open Stallings
open Stallings.CosetEquivalent

theorem Stallings.CosetEquivalent.right_mul {H : Subgroup Free} {g h : Free}
    (gh : CosetEquivalent H g h) (x : Free) : CosetEquivalent H (g * x) (h * x) := by sorry
