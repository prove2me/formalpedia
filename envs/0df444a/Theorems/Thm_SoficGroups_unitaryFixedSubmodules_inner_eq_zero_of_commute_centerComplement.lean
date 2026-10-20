-- Prove2me | Theorems.Thm_SoficGroups_unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
-- name    : SoficGroups.unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/7a05006c-f4f8-4451-9052-62516812a943
-- title:
--   SoficGroups.unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ j : J, Commute (k : G) (j : G))
    (hKZ : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    (hcenter : Z ≤ K ⊔ J)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π K)
    (hb : b ∈ unitaryFixedSubmodule π J)
    (hbZ : b ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    inner ℂ a b = 0 := by sorry
