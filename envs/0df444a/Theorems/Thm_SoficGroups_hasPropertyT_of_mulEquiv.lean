-- Prove2me | Theorems.Thm_SoficGroups_hasPropertyT_of_mulEquiv
-- name    : SoficGroups.hasPropertyT_of_mulEquiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/f4de36c6-5f02-4cec-97a1-54c248f144a8
-- title:
--   SoficGroups.hasPropertyT_of_mulEquiv
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

theorem SoficGroups.hasPropertyT_of_mulEquiv {G : Type u} {G' : Type w}
    [Group G] [Group G'] (e : G ≃* G')
    [HasPropertyT.{u, v} G] : HasPropertyT.{w, v} G' := by sorry
