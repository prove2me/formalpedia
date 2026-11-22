-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_activeLabels_eq
-- name    : Parikh.EncodedGrammar.activeLabels_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:27.341291+00:00
-- url     : https://prove2.me/theorems/cc9a0831-6ab8-40be-bd16-3508705d78df
-- title:
--   Encoded Grammar: active Labels eq
-- statement:
--   The Encoded Grammar construction uses the active Labels eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L36-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L36-L47

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.activeLabels_eq (g : EncodedGrammar) :
    g.activeLabels = activeNonterminals g.decode := by sorry
