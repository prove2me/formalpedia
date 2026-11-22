-- Prove2me | Theorems.Thm_Parikh_dfaGrammar_language
-- name    : Parikh.dfaGrammar_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:48.909482+00:00
-- url     : https://prove2.me/theorems/e16b4e27-4509-4c8d-a3a5-7a848051f68e
-- title:
--   Parikh: dfa Grammar language
-- statement:
--   The finite right-linear grammar generates precisely the DFA's language,
--   including empty words and empty terminal alphabets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/DFAGrammar.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/DFAGrammar.lean#L132-L134

module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]

theorem Parikh.dfaGrammar_language (M : DFA T σ) : (dfaGrammar M).language = M.accepts := by sorry
