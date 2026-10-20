-- Prove2me | Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sum_sq_realIndicator_displacement
-- name    : SoficGroups.KunDirectedIndicatorJensen.sum_sq_realIndicator_displacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/1e781312-fd20-4772-a60f-a623c54b9aa9
-- title:
--   SoficGroups.KunDirectedIndicatorJensen.sum_sq_realIndicator_displacement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators

theorem SoficGroups.KunDirectedIndicatorJensen.sum_sq_realIndicator_displacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realIndicator T (p x) - realIndicator T x) ^ 2) =
      2 * ((T.filter fun x => p x ∉ T).card : ℝ) := by sorry
