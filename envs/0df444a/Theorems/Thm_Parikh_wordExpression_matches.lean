-- Prove2me | Theorems.Thm_Parikh_wordExpression_matches
-- name    : Parikh.wordExpression_matches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:53.354156+00:00
-- url     : https://prove2.me/theorems/00968e4e-c023-4ce4-b5f1-efeb93f82ebb
-- title:
--   Parikh: word Expression matches
-- statement:
--   A literal-word expression accepts exactly that word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L97-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L97-L105

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}

theorem Parikh.wordExpression_matches (w : List T) :
    (wordExpression w).matches' = {w} := by sorry
