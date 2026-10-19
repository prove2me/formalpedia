-- Prove2me | Theorems.Thm_SoficGroups_exists_finitelyPresented_not_sofic_of_not_sofic
-- name    : SoficGroups.exists_finitelyPresented_not_sofic_of_not_sofic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/8925a692-f95d-421a-a758-bd6eea3ce307
-- title:
--   SoficGroups.exists_finitelyPresented_not_sofic_of_not_sofic
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

theorem SoficGroups.exists_finitelyPresented_not_sofic_of_not_sofic
    {G : Type u} [Group G] (hG : ¬ Sofic G) :
    ∃ (H : Type u) (_ : Group H),
      Group.IsFinitelyPresented H ∧ ¬ Sofic H := by sorry
