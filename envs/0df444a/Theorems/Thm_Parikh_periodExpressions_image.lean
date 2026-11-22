-- Prove2me | Theorems.Thm_Parikh_periodExpressions_image
-- name    : Parikh.periodExpressions_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:06.54625+00:00
-- url     : https://prove2.me/theorems/15f6bb54-76a8-41fd-b08c-39e238fa3c2d
-- title:
--   Parikh: period Expressions image
-- statement:
--   The ordered product of starred period words realizes the existing additive
--   closure of the period values; indexed coefficient semantics are reused unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L154-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L154-L176

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

theorem Parikh.periodExpressions_image [DecidableEq T] (alphabet : AlphabetOrder T)
    (periods : List (Vector T)) :
    image (periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches' =
      (AddSubmonoid.closure (Set.range periods.get) : Set (Vector T)) := by sorry
