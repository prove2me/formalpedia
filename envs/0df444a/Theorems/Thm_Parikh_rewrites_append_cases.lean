-- Prove2me | Theorems.Thm_Parikh_rewrites_append_cases
-- name    : Parikh.rewrites_append_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:12.942246+00:00
-- url     : https://prove2.me/theorems/e7f6eb57-39d0-49ab-b1f1-46ee5a6e8491
-- title:
--   Parikh: rewrites append cases
-- statement:
--   A context-free rewrite in a concatenation occurs in one of its two parts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L288-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L288-L301

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

theorem Parikh.rewrites_append_cases (r : ContextFreeRule T N)
    (u v w : List (Symbol T N)) (h : r.Rewrites (u ++ v) w) :
    (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨
      (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by sorry
