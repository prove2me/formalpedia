-- Prove2me | Theorems.Thm_SoficGroups_hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
-- name    : SoficGroups.hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/7195b2cb-94d2-4c79-ab79-568be8cde156
-- title:
--   SoficGroups.hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
universe vSharp

theorem SoficGroups.hasPropertyT_of_finiteOuterBlockCyclicRootFamily_generate
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R) [Finite W]
    (hgen :
      (⨆ i : Fin 3, finiteOuterBlockCyclicRootFamily W i) = ⊤) :
    HasPropertyT.{_, vSharp}
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by sorry
