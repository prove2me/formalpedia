-- Prove2me | Theorems.Thm_Parikh_witnessExpression_correct
-- name    : Parikh.witnessExpression_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:41.296481+00:00
-- url     : https://prove2.me/theorems/6f093752-5e63-487b-85f6-14da88b25f61
-- title:
--   Parikh: witness Expression correct
-- statement:
--   The constructed expression realizes the exact witness and is DFA-regular (`thm:converse`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L251-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L251-L254

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

theorem Parikh.witnessExpression_correct [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation ∧
      (witnessExpression alphabet W).matches'.IsRegular := by sorry
