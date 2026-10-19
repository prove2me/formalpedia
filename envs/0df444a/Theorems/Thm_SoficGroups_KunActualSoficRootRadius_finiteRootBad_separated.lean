-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_separated
-- name    : SoficGroups.KunActualSoficRootRadius.finiteRootBad_separated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/1bcc941e-7164-4155-8aaa-2c39437e34cc
-- title:
--   SoficGroups.KunActualSoficRootRadius.finiteRootBad_separated
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

theorem SoficGroups.KunActualSoficRootRadius.finiteRootBad_separated
    {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hne : g ≠ h)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    M.action g x ≠ M.action h x := by sorry
