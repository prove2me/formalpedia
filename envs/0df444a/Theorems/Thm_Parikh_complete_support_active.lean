-- Prove2me | Theorems.Thm_Parikh_complete_support_active
-- name    : Parikh.complete_support_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:15.426782+00:00
-- url     : https://prove2.me/theorems/c051a989-bd1a-455a-ab7c-7e7a0ea9372c
-- title:
--   Parikh: complete support active
-- statement:
--   Every production node in a complete tree belongs to the finite active alphabet.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L210-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L210-L212

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

theorem Parikh.complete_support_active (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by sorry
