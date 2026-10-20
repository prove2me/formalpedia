-- Prove2me | Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sum_sum_sq_realIndicator_inverse_displacement
-- name    : SoficGroups.KunDirectedIndicatorJensen.sum_sum_sq_realIndicator_inverse_displacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/d76c9632-7ce2-4a7e-a769-40e97bb65424
-- title:
--   SoficGroups.KunDirectedIndicatorJensen.sum_sum_sq_realIndicator_inverse_displacement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators

theorem SoficGroups.KunDirectedIndicatorJensen.sum_sum_sq_realIndicator_inverse_displacement
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ i : ι, ∑ x : V,
      (realIndicator T ((σ i).symm x) - realIndicator T x) ^ 2) =
      2 * (SoficGroups.boundary σ T : ℝ) := by sorry
