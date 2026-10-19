-- Prove2me | Theorems.Thm_SoficGroups_ejThreeResidualEnergy_eq_zero_iff
-- name    : SoficGroups.ejThreeResidualEnergy_eq_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/c684c358-9a7b-4f29-88f6-a341633a8774
-- title:
--   SoficGroups.ejThreeResidualEnergy_eq_zero_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]

theorem SoficGroups.ejThreeResidualEnergy_eq_zero_iff (x : H) :
    ejThreeResidualEnergy V x = 0 ↔
      ∀ i : Fin 3, ejResidualProjection (V i) x = 0 := by sorry
