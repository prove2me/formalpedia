-- Prove2me | Theorems.Thm_Parikh_periodExpressions_regular
-- name    : Parikh.periodExpressions_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:35.926243+00:00
-- url     : https://prove2.me/theorems/2c8935f5-fd40-447b-8b61-c7a807311c01
-- title:
--   Parikh: period Expressions regular
-- statement:
--   Each ordered starred-period product is DFA-regular (`lem:linear-regular`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L219-L231
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L219-L231

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

theorem Parikh.periodExpressions_regular (alphabet : AlphabetOrder T) (periods : List (Vector T)) :
    (periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest)
        .epsilon).matches'.IsRegular := by sorry
