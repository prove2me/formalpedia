-- Prove2me | Theorems.Thm_Research_tri_norm_le_thirtySix_bounds
-- name    : Research.tri_norm_le_thirtySix_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:57:14.656263+00:00
-- url     : https://prove2.me/theorems/84793b81-8a8d-47ba-b2fc-3ee6edceab89
-- title:
--   Research: tri norm le thirty Six bounds
-- statement:
--   Any triangular-lattice coordinate of squared norm at most 36 lies in the
--   `[-6,6]²` census window.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L160-L183
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L160-L183

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.tri_norm_le_thirtySix_bounds (m n : ℤ)
    (h : triNormSq (m, n) ≤ 36) :
    -6 ≤ m ∧ m ≤ 6 ∧ -6 ≤ n ∧ n ≤ 6 := by sorry
