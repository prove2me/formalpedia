-- Prove2me | Theorems.Thm_SoficGroups_finiteOuterBlockCyclicRootFamily_iSup_eq_top
-- name    : SoficGroups.finiteOuterBlockCyclicRootFamily_iSup_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/eee84617-7744-4959-8808-145c9a61355b
-- title:
--   SoficGroups.finiteOuterBlockCyclicRootFamily_iSup_eq_top
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators

theorem SoficGroups.finiteOuterBlockCyclicRootFamily_iSup_eq_top
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (s : Finset R)
    (hs : Algebra.adjoin (ZMod 2) (↑s : Set R) = ⊤) :
    (⨆ i : Fin 3,
      finiteOuterBlockCyclicRootFamily (finiteBlockCoefficientSpan s) i) =
        ⊤ := by sorry
