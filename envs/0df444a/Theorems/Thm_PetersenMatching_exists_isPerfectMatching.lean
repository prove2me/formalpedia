-- Prove2me | Theorems.Thm_PetersenMatching_exists_isPerfectMatching
-- name    : PetersenMatching.exists_isPerfectMatching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:49:06.929828+00:00
-- url     : https://prove2.me/theorems/e36f3bc6-61b7-5ba9-8905-040fac1279cb
-- title:
--   Petersen Matching: exists is Perfect Matching
-- statement:
--   **Petersen's theorem (1891).** A finite bridgeless cubic graph has a perfect matching.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/Solution.lean#L30-L33
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/Solution.lean#L30-L33

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Definitions.Def_PetersenMatching_Solution
public import Theorems.Thm_PetersenTheorem_exists_isPerfectMatching

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenMatching
variable {V : Type*}

theorem PetersenMatching.exists_isPerfectMatching [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by sorry
