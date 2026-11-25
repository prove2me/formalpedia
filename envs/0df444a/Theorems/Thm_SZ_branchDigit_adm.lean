-- Prove2me | Theorems.Thm_SZ_branchDigit_adm
-- name    : SZ.branchDigit_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:35.204747+00:00
-- url     : https://prove2.me/theorems/82b135c0-2065-528c-afc9-af6eafdd4b6c
-- title:
--   SZ: branch Digit adm
-- statement:
--   Both offsets are admissible on `O`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L566-L588
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L566-L588

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.branchDigit_adm {w : ℝ} (h : InO w) (b : Bool) :
    0 ≤ w - valS (branchDigit w b) ∧ w - valS (branchDigit w b) ≤ 1 + Real.sqrt 3 := by sorry
