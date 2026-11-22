-- Prove2me | Theorems.Thm_Parikh_representative_counts
-- name    : Parikh.representative_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:54.401968+00:00
-- url     : https://prove2.me/theorems/4edfd183-c8e0-421f-8cde-1d9fd8b5c2cb
-- title:
--   Parikh: representative counts
-- statement:
--   Representative words have exactly the prescribed counts (`eq:representative`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L83-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L83-L94

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

theorem Parikh.representative_counts [DecidableEq T] (alphabet : AlphabetOrder T) (v : Vector T) :
    counts (representative alphabet v) = v := by sorry
