-- Prove2me | Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_normalizedHamming_mul_le
-- name    : SoficGroups.CompletedChosenWordLocalRoot.normalizedHamming_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/6f73facf-d8e8-4c0c-9402-ec8d09758d3f
-- title:
--   SoficGroups.CompletedChosenWordLocalRoot.normalizedHamming_mul_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators

theorem SoficGroups.CompletedChosenWordLocalRoot.normalizedHamming_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (p p' q q' : Equiv.Perm V) :
    SoficGroups.normalizedHamming (p * q) (p' * q') ≤
      SoficGroups.normalizedHamming p p' +
        SoficGroups.normalizedHamming q q' := by sorry
