-- Prove2me | Theorems.Thm_Parikh_ParseTree_exists_labelPath_height
-- name    : Parikh.ParseTree.exists_labelPath_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:46.765199+00:00
-- url     : https://prove2.me/theorems/aa16e89a-053a-4bb5-bbb0-3c51ba853c84
-- title:
--   Parse Tree: exists label Path height
-- statement:
--   A longest production-label path realizes production height (`def:statistics`).
--   An empty-production node has the singleton root path; terminals and holes have the empty path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ParseTreePaths.lean#L70-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ParseTreePaths.lean#L70-L94

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
set_option autoImplicit true
@[expose] public section
public section
open Parikh Parikh.ParseTree
variable {T N : Type*}

theorem Parikh.ParseTree.exists_labelPath_height (t : ParseTree T N) :
    ∃ path ∈ t.labelPaths, path.length = t.height := by sorry
