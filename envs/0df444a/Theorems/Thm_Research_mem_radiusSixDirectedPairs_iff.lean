-- Prove2me | Theorems.Thm_Research_mem_radiusSixDirectedPairs_iff
-- name    : Research.mem_radiusSixDirectedPairs_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:55.915569+00:00
-- url     : https://prove2.me/theorems/77dd5376-651a-420b-9692-71934a86a4ce
-- title:
--   Research: mem radius Six Directed Pairs iff
-- statement:
--   The Research construction uses the mem radius Six Directed Pairs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L409-L413
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L409-L413

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.mem_radiusSixDirectedPairs_iff {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q ∈ radiusSixDirectedPairs p ↔
      q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) ≤ 36 := by sorry
