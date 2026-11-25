-- Prove2me | Theorems.Thm_PetersenTheorem_exists_isPerfectMatching_mem
-- name    : PetersenTheorem.exists_isPerfectMatching_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:27.934529+00:00
-- url     : https://prove2.me/theorems/cf228d1b-07b2-40b0-8a34-60914f323741
-- title:
--   Petersen Theorem: exists is Perfect Matching mem
-- statement:
--   In a finite bridgeless cubic graph every edge lies in some perfect matching.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L222-L359
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L222-L359

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}

theorem PetersenTheorem.exists_isPerfectMatching_mem [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∀ e ∈ G.edgeSet, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet := by sorry
