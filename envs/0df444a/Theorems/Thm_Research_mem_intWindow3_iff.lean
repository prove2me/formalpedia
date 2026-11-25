-- Prove2me | Theorems.Thm_Research_mem_intWindow3_iff
-- name    : Research.mem_intWindow3_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:16.599828+00:00
-- url     : https://prove2.me/theorems/06f642ff-255c-42de-ac6a-31eb09b2d29d
-- title:
--   Research: mem int Window3 iff
-- statement:
--   Membership characterization of the executable coordinate window.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L56-L59
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/TriangularShells.lean#L56-L59

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.mem_intWindow3_iff (z : ℤ) :
    z ∈ intWindow3 ↔ -3 ≤ z ∧ z ≤ 3 := by sorry
