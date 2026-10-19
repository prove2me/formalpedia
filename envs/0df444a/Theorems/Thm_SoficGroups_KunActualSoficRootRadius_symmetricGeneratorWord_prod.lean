-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
-- name    : SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/13eb238d-c7b7-4128-9345-786b43df76ba
-- title:
--   SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_prod
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

theorem SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_prod
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) :
    (((symmetricGeneratorWord S hsymmetric hgenerates g).map
      fun i : ↥S => (i : G)).prod) = g := by sorry
