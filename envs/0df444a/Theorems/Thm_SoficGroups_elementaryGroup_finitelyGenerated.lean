-- Prove2me | Theorems.Thm_SoficGroups_elementaryGroup_finitelyGenerated
-- name    : SoficGroups.elementaryGroup_finitelyGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/6051f8e4-8b12-4372-be9e-d7eebf27f439
-- title:
--   SoficGroups.elementaryGroup_finitelyGenerated
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

theorem SoficGroups.elementaryGroup_finitelyGenerated
    [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by sorry
