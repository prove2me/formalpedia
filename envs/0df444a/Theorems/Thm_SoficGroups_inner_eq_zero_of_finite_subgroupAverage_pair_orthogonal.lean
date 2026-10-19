-- Prove2me | Theorems.Thm_SoficGroups_inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
-- name    : SoficGroups.inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/922a8b13-a523-451c-a8f6-7fe2798419d4
-- title:
--   SoficGroups.inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SoficGroups.inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
    (π : UnitaryRepresentation G H)
    (K J : Subgroup G) [Fintype K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a)
    (horbit : ∀ (k : K) (j : J),
      π (j : G) (π (k : G) b) = π (k : G) b)
    (horth : ∀ z : H,
      (∀ k : K, π (k : G) z = z) →
      (∀ j : J, π (j : G) z = z) →
      inner ℂ a z = 0) :
    inner ℂ a b = 0 := by sorry
