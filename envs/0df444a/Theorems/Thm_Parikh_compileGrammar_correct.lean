-- Prove2me | Theorems.Thm_Parikh_compileGrammar_correct
-- name    : Parikh.compileGrammar_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:58.072678+00:00
-- url     : https://prove2.me/theorems/2d728e24-c87c-488b-af99-1abefbfbb43f
-- title:
--   Parikh: compile Grammar correct
-- statement:
--   The computed representation denotes exactly the grammar's Parikh image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L104-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L104-L105

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

theorem Parikh.compileGrammar_correct (g : EncodedGrammar) :
    (compileGrammar g).denotation = parikhImage g.decode.language := by sorry
