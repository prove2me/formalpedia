-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdan_generator_displacement_of_orthogonal_invariants
-- name    : SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_displacement_of_orthogonal_invariants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/aaadcbb3-cf85-49fb-98a5-59ee6c2f8409
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_displacement_of_orthogonal_invariants
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_displacement_of_orthogonal_invariants
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H) (x : H)
    (hx : x ≠ 0)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖x‖ ≤ ‖π g x - x‖ := by sorry
