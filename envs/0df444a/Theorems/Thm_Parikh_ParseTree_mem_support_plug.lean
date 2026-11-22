-- Prove2me | Theorems.Thm_Parikh_ParseTree_mem_support_plug
-- name    : Parikh.ParseTree.mem_support_plug
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:22.114517+00:00
-- url     : https://prove2.me/theorems/965cb883-e05c-4840-bbc0-e1f6472d655f
-- title:
--   Parse Tree: mem support plug
-- statement:
--   Plugging adds the inserted support exactly when the context has a hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L110-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L110-L133

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreePlugging
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.mem_support_plug (E t : ParseTree T N) (A : N) :
    A ∈ (E.plug t).support ↔ A ∈ E.support ∨ (E.holes ≠ [] ∧ A ∈ t.support) := by sorry
