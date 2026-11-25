-- Prove2me | Theorems.Thm_PetersenTheorem_exists_isPerfectMatching
-- name    : PetersenTheorem.exists_isPerfectMatching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:32.26544+00:00
-- url     : https://prove2.me/theorems/93405b84-215e-4b7e-8760-ce0cd8fbeb5a
-- title:
--   Petersen Theorem: exists is Perfect Matching
-- statement:
--   **Petersen's theorem (1891).** A finite bridgeless cubic graph has a perfect matching.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L207-L219
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L207-L219

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}

theorem PetersenTheorem.exists_isPerfectMatching [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by sorry
