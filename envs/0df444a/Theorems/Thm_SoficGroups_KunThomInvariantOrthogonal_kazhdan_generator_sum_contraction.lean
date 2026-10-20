-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdan_generator_sum_contraction
-- name    : SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_sum_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/69c9dcf5-2c01-4a01-a5b0-f5c16f3a6268
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_sum_contraction
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

theorem SoficGroups.KunThomInvariantOrthogonal.kazhdan_generator_sum_contraction
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0) :
    ‖∑ g ∈ S, π g x‖ ≤
      ((S.card : ℝ) - P.kazhdanConstant ^ 2 / 4) * ‖x‖ := by sorry
