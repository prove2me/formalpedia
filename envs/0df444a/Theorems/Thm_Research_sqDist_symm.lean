-- Prove2me | Theorems.Thm_Research_sqDist_symm
-- name    : Research.sqDist_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:58:05.051584+00:00
-- url     : https://prove2.me/theorems/8226fa34-5ab7-4da9-b442-184342b8da19
-- title:
--   Research: sq Dist symm
-- statement:
--   The Research construction uses the sq Dist symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L536-L538
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L536-L538

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.sqDist_symm (p q : ℝ × ℝ) : sqDist p q = sqDist q p := by sorry
