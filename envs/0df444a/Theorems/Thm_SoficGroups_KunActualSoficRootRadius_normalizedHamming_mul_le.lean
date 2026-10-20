-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_normalizedHamming_mul_le
-- name    : SoficGroups.KunActualSoficRootRadius.normalizedHamming_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/c6b478e7-7335-40a9-9af0-c515cc98b805
-- title:
--   SoficGroups.KunActualSoficRootRadius.normalizedHamming_mul_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSoficRootRadius.normalizedHamming_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (p p' q q' : Equiv.Perm V) :
    SoficGroups.normalizedHamming (p * q) (p' * q') ≤
      SoficGroups.normalizedHamming p p' +
        SoficGroups.normalizedHamming q q' := by sorry
