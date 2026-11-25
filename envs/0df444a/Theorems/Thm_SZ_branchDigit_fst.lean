-- Prove2me | Theorems.Thm_SZ_branchDigit_fst
-- name    : SZ.branchDigit_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:16:44.94008+00:00
-- url     : https://prove2.me/theorems/504b2cae-5223-59c7-8067-b82d3c9ea5a7
-- title:
--   SZ: branch Digit fst
-- statement:
--   **The two offsets differ in their `a`-part** — this is what separates the witnesses.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L554-L555
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L554-L555

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.branchDigit_fst (w : ℝ) (b : Bool) : (branchDigit w b).1 = cond b 2 0 := by sorry
