-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_high_variation_le_of_markov_square_bounds
-- name    : SoficGroups.KunActualFinalRestrictedVariation.high_variation_le_of_markov_square_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/784eb884-cdc2-4b52-af6e-fff1c74eda21
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.high_variation_le_of_markov_square_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.high_variation_le_of_markov_square_bounds
    {d t α η b r E H : ℝ}
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ t)
    (hresidual : r ≤ η * b)
    (henergy : E ≤ 2 * d * Real.sqrt t * r)
    (hcauchy : H ^ 2 ≤ 3 * d * t * E)
    (hsmall : 486 * d ^ 2 * η ≤ 4 * α ^ 2) :
    9 * H ≤ 2 * α * t := by sorry
