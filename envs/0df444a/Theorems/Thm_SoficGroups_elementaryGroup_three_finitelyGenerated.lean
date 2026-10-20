-- Prove2me | Theorems.Thm_SoficGroups_elementaryGroup_three_finitelyGenerated
-- name    : SoficGroups.elementaryGroup_three_finitelyGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/44162698-2731-4f5b-8a8d-ca989456fc81
-- title:
--   SoficGroups.elementaryGroup_three_finitelyGenerated
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {R : Type*} [Ring R]
variable [Algebra (ZMod 2) R]

theorem SoficGroups.elementaryGroup_three_finitelyGenerated
    [Algebra.FiniteType (ZMod 2) R] :
    Group.FG (elementaryGroup (Fin 3) R) := by sorry
