-- Prove2me | Theorems.Thm_Research_obliqueNormNum_ge_denominator
-- name    : Research.obliqueNormNum_ge_denominator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:56:44.183558+00:00
-- url     : https://prove2.me/theorems/d0d5f1d9-01e4-4285-bae1-27df10e4ad62
-- title:
--   Research: oblique Norm Num ge denominator
-- statement:
--   Every nonzero integer offset has squared distance at least one.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L74-L104
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L74-L104

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueNormNum_ge_denominator (m n : ℤ)
    (hne : (m, n) ≠ (0, 0)) : 305 ≤ obliqueNormNum (m, n) := by sorry
