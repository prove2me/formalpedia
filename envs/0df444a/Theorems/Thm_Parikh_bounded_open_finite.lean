-- Prove2me | Theorems.Thm_Parikh_bounded_open_finite
-- name    : Parikh.bounded_open_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:13.746718+00:00
-- url     : https://prove2.me/theorems/9bb5c78f-8957-4be5-90f1-bcc3cf38bf7e
-- title:
--   Parikh: bounded open finite
-- statement:
--   Finite terminals and finite productions suffice; no `Fintype g.NT` (`lem:finite`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L215-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L215-L282

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

theorem Parikh.bounded_open_finite [Finite T] (g : ContextFreeGrammar T) (H : ℕ) :
    {t : ParseTree T g.NT | ActiveOpen g t ∧ t.height ≤ H}.Finite := by sorry
