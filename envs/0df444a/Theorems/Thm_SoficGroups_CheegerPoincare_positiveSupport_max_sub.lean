-- Prove2me | Theorems.Thm_SoficGroups_CheegerPoincare_positiveSupport_max_sub
-- name    : SoficGroups.CheegerPoincare.positiveSupport_max_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/17added9-0418-4070-aea2-fd6d76bc928a
-- title:
--   SoficGroups.CheegerPoincare.positiveSupport_max_sub
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

theorem SoficGroups.CheegerPoincare.positiveSupport_max_sub {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (f x - m) 0) = upperLevel f m := by sorry
