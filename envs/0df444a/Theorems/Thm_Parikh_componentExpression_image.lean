-- Prove2me | Theorems.Thm_Parikh_componentExpression_image
-- name    : Parikh.componentExpression_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:12.180979+00:00
-- url     : https://prove2.me/theorems/a380a5cb-1491-492b-aa3e-de8f50373446
-- title:
--   Parikh: component Expression image
-- statement:
--   The component expression has exactly the frozen indexed linear denotation
--   (`lem:linear-regular`); DFA regularity is proved separately.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L180-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L180-L195

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

theorem Parikh.componentExpression_image [DecidableEq T] (alphabet : AlphabetOrder T)
    (c : Component T) :
    image (componentExpression alphabet c).matches' = c.denotation := by sorry
