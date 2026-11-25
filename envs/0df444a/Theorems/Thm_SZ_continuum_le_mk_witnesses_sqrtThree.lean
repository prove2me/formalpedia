-- Prove2me | Theorems.Thm_SZ_continuum_le_mk_witnesses_sqrtThree
-- name    : SZ.continuum_le_mk_witnesses_sqrtThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:02:43.084284+00:00
-- url     : https://prove2.me/theorems/db8a42ad-3492-4af8-8174-5ea37ea87cd4
-- title:
--   SZ: continuum le mk witnesses sqrt Three
-- statement:
--   **Theorem 9.1, cardinality half**, with `W` written out.  The statement of
--   `continuum_le_mk_witnessSet` with `witnessSet` unfolded, so that it names nothing outside
--   Mathlib; this is the form `Challenge.lean` certifies (see `COMPARATOR.md`).
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1192-L1195
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1192-L1195

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.continuum_le_mk_witnesses_sqrtThree :
    Cardinal.continuum ≤
      Cardinal.mk {ξ : ℝ | 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋} := by sorry
