-- Prove2me | Theorems.Thm_SoficGroups_normalizedHamming_mul_left
-- name    : SoficGroups.normalizedHamming_mul_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/3eea543d-d63e-43db-b5a4-a482451a02b5
-- title:
--   SoficGroups.normalizedHamming_mul_left
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

theorem SoficGroups.normalizedHamming_mul_left {Y : Type*} [Fintype Y] [DecidableEq Y]
    (s p q : Equiv.Perm Y) :
    normalizedHamming (s * p) (s * q) = normalizedHamming p q := by sorry
