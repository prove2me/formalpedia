-- Prove2me | Theorems.Thm_Research_swap_mem_radiusSixDirectedPairs_iff
-- name    : Research.swap_mem_radiusSixDirectedPairs_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:58:22.490874+00:00
-- url     : https://prove2.me/theorems/311bf68f-1b80-48c0-940c-32b86ac39c49
-- title:
--   Research: swap mem radius Six Directed Pairs iff
-- statement:
--   The Research construction uses the swap mem radius Six Directed Pairs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L540-L550
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L540-L550

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.swap_mem_radiusSixDirectedPairs_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q.swap ∈ radiusSixDirectedPairs p ↔ q ∈ radiusSixDirectedPairs p := by sorry
