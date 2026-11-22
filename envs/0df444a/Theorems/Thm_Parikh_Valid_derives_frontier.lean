-- Prove2me | Theorems.Thm_Parikh_Valid_derives_frontier
-- name    : Parikh.Valid.derives_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:15.128748+00:00
-- url     : https://prove2.me/theorems/be77cf54-fec6-40d5-a8be-524b6d01e5d6
-- title:
--   Valid: derives frontier
-- statement:
--   A valid tree gives a Mathlib derivation from its root to its frontier.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L367-L387
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L367-L387

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
variable {N : Type*}

theorem Parikh.Valid.derives_frontier {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : g.Derives [t.root] t.frontier := by sorry
