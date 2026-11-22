-- Prove2me | Theorems.Thm_Parikh_componentExpression_regular
-- name    : Parikh.componentExpression_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:39.563258+00:00
-- url     : https://prove2.me/theorems/91786554-9780-4f21-882c-68a36d14e064
-- title:
--   Parikh: component Expression regular
-- statement:
--   The base-word prefix preserves the regularity of the period product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L234-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L234-L240

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

theorem Parikh.componentExpression_regular (alphabet : AlphabetOrder T) (c : Component T) :
    (componentExpression alphabet c).matches'.IsRegular := by sorry
