-- Prove2me | Theorems.Thm_Parikh_witnessExpression_image
-- name    : Parikh.witnessExpression_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:17.245004+00:00
-- url     : https://prove2.me/theorems/54676e19-7a96-4f5f-91d9-7a0282397460
-- title:
--   Parikh: witness Expression image
-- statement:
--   Exact-image half of `witnessExpression_correct`, proved independently of the
--   DFA clause (`eq:regular-construction`, `thm:converse`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L199-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L199-L216

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

theorem Parikh.witnessExpression_image [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation := by sorry
