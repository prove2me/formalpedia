-- Prove2me | Theorems.Thm_SoficGroups_component_omitted_rank_card_eq
-- name    : SoficGroups.component_omitted_rank_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/9cd462ce-c908-4eae-b302-b7908a05c101
-- title:
--   SoficGroups.component_omitted_rank_card_eq
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

theorem SoficGroups.component_omitted_rank_card_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ)
    (hC : C.Nonempty) :
    ((C.card - (C.filter fun x => b x = j).card : ℕ) : ℝ) =
      (C.card : ℝ) * (1 - componentRankMass C b j) := by sorry
