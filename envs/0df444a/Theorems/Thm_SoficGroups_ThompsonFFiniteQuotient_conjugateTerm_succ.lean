-- Prove2me | Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugateTerm_succ
-- name    : SoficGroups.ThompsonFFiniteQuotient.conjugateTerm_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/c0a93559-0076-405b-bc7f-da8409031569
-- title:
--   SoficGroups.ThompsonFFiniteQuotient.conjugateTerm_succ
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]

theorem SoficGroups.ThompsonFFiniteQuotient.conjugateTerm_succ (a b : G) (n : ℕ) :
    conjugateTerm a b (n + 1) =
      a⁻¹ * conjugateTerm a b n * a := by sorry
