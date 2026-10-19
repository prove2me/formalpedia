-- Prove2me | Theorems.Thm_SoficGroups_CheegerPoincare_positiveSupport_max_sub_reverse
-- name    : SoficGroups.CheegerPoincare.positiveSupport_max_sub_reverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/04dcd1a6-18bf-4eee-8344-1b9878d47726
-- title:
--   SoficGroups.CheegerPoincare.positiveSupport_max_sub_reverse
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
open SoficGroups.CheegerPoincare
open scoped BigOperators

theorem SoficGroups.CheegerPoincare.positiveSupport_max_sub_reverse {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (m - f x) 0) = lowerLevel f m := by sorry
