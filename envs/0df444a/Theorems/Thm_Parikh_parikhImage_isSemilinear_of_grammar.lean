-- Prove2me | Theorems.Thm_Parikh_parikhImage_isSemilinear_of_grammar
-- name    : Parikh.parikhImage_isSemilinear_of_grammar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:54.855389+00:00
-- url     : https://prove2.me/theorems/d60f19a9-8aa0-4a8a-a243-0fcaecde5fd6
-- title:
--   Parikh: parikh Image is Semilinear of grammar
-- statement:
--   The Parikh image of a context-free grammar is semilinear.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L66-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L66-L67

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.parikhImage_isSemilinear_of_grammar {T : Type*} [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (parikhImage g.language) := by sorry
