-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_cycleTest_correct
-- name    : Parikh.EncodedGrammar.cycleTest_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:35.083853+00:00
-- url     : https://prove2.me/theorems/40fd554f-ec8b-4d88-a247-7e0e9fef437a
-- title:
--   Encoded Grammar: cycle Test correct
-- statement:
--   The Encoded Grammar construction uses the cycle Test correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L83-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L83-L93

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.cycleTest_correct (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode C) : g.cycleTest C = true ↔ IsBoundedCycle g.decode C := by sorry
