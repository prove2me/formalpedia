-- Prove2me | Theorems.Thm_Parikh_Valid_support_active
-- name    : Parikh.Valid.support_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:10.773233+00:00
-- url     : https://prove2.me/theorems/393bfd90-03a3-4a88-a912-b18feac46dce
-- title:
--   Valid: support active
-- statement:
--   Production-node labels are active even in a valid open tree (`def:statistics`).
--   Holes contribute no label to support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L182-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L182-L207

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.Valid.support_active {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by sorry
