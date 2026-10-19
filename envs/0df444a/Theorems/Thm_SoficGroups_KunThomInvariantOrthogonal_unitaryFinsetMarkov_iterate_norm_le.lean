-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_unitaryFinsetMarkov_iterate_norm_le
-- name    : SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_iterate_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/7079c0b1-8fd5-4fdc-88b2-96dc97db1118
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_iterate_norm_le
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

theorem SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_iterate_norm_le
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0)
    (n : ℕ) :
    ‖((unitaryFinsetMarkov π S)^[n]) x‖ ≤
      kazhdanMarkovContractionFactor P S ^ n * ‖x‖ := by sorry
