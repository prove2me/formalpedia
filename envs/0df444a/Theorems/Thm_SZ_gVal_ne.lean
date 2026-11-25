-- Prove2me | Theorems.Thm_SZ_gVal_ne
-- name    : SZ.gVal_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:17.932334+00:00
-- url     : https://prove2.me/theorems/18e31507-c958-48e2-97f6-05dee60a7a29
-- title:
--   SZ: g Val ne
-- statement:
--   No state of the rule's orbit is a trap fixed point.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L211-L214
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L211-L214

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gVal_ne {s : ℤ × ℤ} (h : GStart s) (k : ℕ) {p q : ℤ} (hq : q ≤ 3) :
    valS (gState s k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by sorry
