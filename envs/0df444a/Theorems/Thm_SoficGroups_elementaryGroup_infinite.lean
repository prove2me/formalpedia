-- Prove2me | Theorems.Thm_SoficGroups_elementaryGroup_infinite
-- name    : SoficGroups.elementaryGroup_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/34814255-54b9-4375-8974-89d4973ba22e
-- title:
--   SoficGroups.elementaryGroup_infinite
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
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

theorem SoficGroups.elementaryGroup_infinite [Infinite R] (i j : ι) (h : i ≠ j) :
    Infinite (elementaryGroup ι R) := by sorry
