-- Prove2me | Theorems.Thm_Parikh_ParseTree_labelPath_subset_support
-- name    : Parikh.ParseTree.labelPath_subset_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:35.563205+00:00
-- url     : https://prove2.me/theorems/07c242af-8efe-489e-bc37-d40d885a0ce1
-- title:
--   Parse Tree: label Path subset support
-- statement:
--   Every production label on a path belongs to the tree's support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ParseTreePaths.lean#L34-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ParseTreePaths.lean#L34-L66

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
set_option autoImplicit true
@[expose] public section
public section
open Parikh Parikh.ParseTree
variable {T N : Type*}

theorem Parikh.ParseTree.labelPath_subset_support (t : ParseTree T N) (path : List N)
    (hpath : path ∈ t.labelPaths) : ∀ A ∈ path, A ∈ t.support := by sorry
