-- Prove2me | Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugacy_relation_of_commute
-- name    : SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/e7d5e5a0-e7bf-4c9b-82f8-e51b34f03ed1
-- title:
--   SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_of_commute
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]

theorem SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_of_commute (a b : G) (n : ℕ)
    (h : Commute (a * b⁻¹) (conjugateTerm a b n)) :
    b⁻¹ * conjugateTerm a b n * b =
      conjugateTerm a b (n + 1) := by sorry
