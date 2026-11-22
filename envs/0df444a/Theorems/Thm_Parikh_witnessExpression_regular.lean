-- Prove2me | Theorems.Thm_Parikh_witnessExpression_regular
-- name    : Parikh.witnessExpression_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:42.350311+00:00
-- url     : https://prove2.me/theorems/e2e5a4e2-49b8-458f-813c-22d7430cb634
-- title:
--   Parikh: witness Expression regular
-- statement:
--   Mathlib's existing finite-union regularity combines the component automata.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L243-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L243-L248

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

theorem Parikh.witnessExpression_regular (alphabet : AlphabetOrder T) (W : Witness T) :
    (witnessExpression alphabet W).matches'.IsRegular := by sorry
