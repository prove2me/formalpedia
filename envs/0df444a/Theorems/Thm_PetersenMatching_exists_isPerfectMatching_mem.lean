-- Prove2me | Theorems.Thm_PetersenMatching_exists_isPerfectMatching_mem
-- name    : PetersenMatching.exists_isPerfectMatching_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:13.990515+00:00
-- url     : https://prove2.me/theorems/3607fcc9-58dd-55b8-92d0-8abf8dbcebf3
-- title:
--   Petersen Matching: exists is Perfect Matching mem
-- statement:
--   In a finite bridgeless cubic graph every edge lies in some perfect matching.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/Solution.lean#L36-L39
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/Solution.lean#L36-L39

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Definitions.Def_PetersenMatching_Solution
public import Theorems.Thm_PetersenTheorem_exists_isPerfectMatching_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenMatching
variable {V : Type*}

theorem PetersenMatching.exists_isPerfectMatching_mem [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∀ e ∈ G.edgeSet, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet := by sorry
