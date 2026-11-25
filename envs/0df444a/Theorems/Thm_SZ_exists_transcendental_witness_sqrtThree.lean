-- Prove2me | Theorems.Thm_SZ_exists_transcendental_witness_sqrtThree
-- name    : SZ.exists_transcendental_witness_sqrtThree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:45.400064+00:00
-- url     : https://prove2.me/theorems/247ef4aa-642c-5e4d-9713-83fc6d7d69df
-- title:
--   SZ: exists transcendental witness sqrt Three
-- statement:
--   **[Dub06EO] Problem 3 has a transcendental witness.**  The statement of
--   `SZ.sqrtThree_mem_MahlerZ` with `ξ` transcendental over `ℚ`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1214-L1218
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L1214-L1218

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.exists_transcendental_witness_sqrtThree :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ Transcendental ℚ ξ ∧
      ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋ := by sorry
