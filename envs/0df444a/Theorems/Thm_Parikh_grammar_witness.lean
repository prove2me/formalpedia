-- Prove2me | Theorems.Thm_Parikh_grammar_witness
-- name    : Parikh.grammar_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:56.974036+00:00
-- url     : https://prove2.me/theorems/26177208-62c5-4da8-80c5-974a0168329e
-- title:
--   Parikh: grammar witness
-- statement:
--   A finite indexed witness with exact denotation, not merely containment (`thm:main`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L53-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Statements.lean#L53-L55

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.grammar_witness [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language := by sorry
