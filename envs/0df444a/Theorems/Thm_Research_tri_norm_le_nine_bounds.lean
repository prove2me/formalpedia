-- Prove2me | Theorems.Thm_Research_tri_norm_le_nine_bounds
-- name    : Research.tri_norm_le_nine_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:06.332144+00:00
-- url     : https://prove2.me/theorems/f1642f99-5b56-462e-94ed-604980aa2571
-- title:
--   Research: tri norm le nine bounds
-- statement:
--   Every coordinate vector of triangular norm squared at most nine lies in the
--   `[-3,3]^2` enumeration window.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L32-L53
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L32-L53

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.tri_norm_le_nine_bounds (a b : ℤ)
    (h : a ^ 2 + a * b + b ^ 2 ≤ 9) :
    -3 ≤ a ∧ a ≤ 3 ∧ -3 ≤ b ∧ b ≤ 3 := by sorry
