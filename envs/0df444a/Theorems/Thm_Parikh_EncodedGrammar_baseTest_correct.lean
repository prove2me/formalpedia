-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_baseTest_correct
-- name    : Parikh.EncodedGrammar.baseTest_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:44.35984+00:00
-- url     : https://prove2.me/theorems/ba0d8c41-6e8a-4ee8-bb1d-928f32316925
-- title:
--   Encoded Grammar: base Test correct
-- statement:
--   The Encoded Grammar construction uses the base Test correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L66-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L66-L75

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.baseTest_correct (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode B) : g.baseTest B = true ↔ IsBase g.decode B := by sorry
