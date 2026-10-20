-- Prove2me | Theorems.Thm_SoficGroups_unitaryFixedSubmodule_sup
-- name    : SoficGroups.unitaryFixedSubmodule_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/5512b8d0-3697-4276-9034-ceef97ce3cf7
-- title:
--   SoficGroups.unitaryFixedSubmodule_sup
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryFixedSubmodule_sup
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    unitaryFixedSubmodule π (K ⊔ J) =
      unitaryFixedSubmodule π K ⊓ unitaryFixedSubmodule π J := by sorry
