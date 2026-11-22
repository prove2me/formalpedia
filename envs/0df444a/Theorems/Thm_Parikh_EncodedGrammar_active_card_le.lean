-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_active_card_le
-- name    : Parikh.EncodedGrammar.active_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:35.924852+00:00
-- url     : https://prove2.me/theorems/1761a96f-d94e-42ae-ad99-bc8b30d85c9e
-- title:
--   Encoded Grammar: active card le
-- statement:
--   The active alphabet is bounded by the declared finite nonterminal count.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L50-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L50-L57

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.active_card_le (g : EncodedGrammar) :
    (activeNonterminals g.decode).card ≤ g.size.nonterminals := by sorry
