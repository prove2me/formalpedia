-- Prove2me | Theorems.Thm_SoficGroups_kazhdan_generator_displacement
-- name    : SoficGroups.kazhdan_generator_displacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/ab1aec8a-c6af-436b-be3f-bfb6d6a3678f
-- title:
--   SoficGroups.kazhdan_generator_displacement
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
universe u₁ u₂ u₃

theorem SoficGroups.kazhdan_generator_displacement
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (hfixed : ∀ η : H, (∀ g : G, π g η = η) → η = 0)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖ξ‖ ≤ ‖π g ξ - ξ‖ := by sorry
