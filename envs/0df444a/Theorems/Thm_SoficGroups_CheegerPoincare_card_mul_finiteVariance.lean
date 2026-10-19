-- Prove2me | Theorems.Thm_SoficGroups_CheegerPoincare_card_mul_finiteVariance
-- name    : SoficGroups.CheegerPoincare.card_mul_finiteVariance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/fddf83af-d50b-4191-bacb-4456ef57e50e
-- title:
--   SoficGroups.CheegerPoincare.card_mul_finiteVariance
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

theorem SoficGroups.CheegerPoincare.card_mul_finiteVariance {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (Fintype.card V : ℝ) * finiteVariance f =
      ∑ x : V, (f x - finiteMean f) ^ 2 := by sorry
