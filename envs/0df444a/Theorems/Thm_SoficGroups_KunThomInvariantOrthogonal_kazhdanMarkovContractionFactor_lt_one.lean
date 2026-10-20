-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
-- name    : SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/15e3a7d0-ea8a-4a92-b0a9-093217c9195a
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
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

theorem SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
    (P : SoficGroups.KazhdanPair.{u, v} G)
    (S : Finset G) (hS : S.Nonempty) :
    kazhdanMarkovContractionFactor P S < 1 := by sorry
