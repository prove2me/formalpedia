-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterBlockRootSubgroup_map_flatten
-- name    : SoficGroups.finiteOuterBlockRootSubgroup_map_flatten
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/a96073a2-6c83-415b-9cee-7e2f778bf4e8
-- title:
--   SoficGroups.finiteOuterBlockRootSubgroup_map_flatten
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators

theorem SoficGroups.finiteOuterBlockRootSubgroup_map_flatten
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) :
    (finiteOuterBlockRootSubgroup W i j hij).map
      (finiteOuterBlockFlattenHom (R := R)) =
        finiteBlockRootSubgroup W i j hij := by sorry
