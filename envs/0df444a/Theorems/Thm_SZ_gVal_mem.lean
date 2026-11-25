-- Prove2me | Theorems.Thm_SZ_gVal_mem
-- name    : SZ.gVal_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:36.676986+00:00
-- url     : https://prove2.me/theorems/a3211e5f-13e3-410c-aef7-bd8b6072b4ab
-- title:
--   SZ: g Val mem
-- statement:
--   **The invariant for the rule from an arbitrary start** (Cover Lemma, by induction).
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L172-L183
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L172-L183

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gVal_mem {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    0 ≤ valS (gState s k) ∧ valS (gState s k) ≤ 3 + 3 * Real.sqrt 3 := by sorry
