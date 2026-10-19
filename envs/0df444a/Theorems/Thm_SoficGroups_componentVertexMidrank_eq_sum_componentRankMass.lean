-- Prove2me | Theorems.Thm_SoficGroups_componentVertexMidrank_eq_sum_componentRankMass
-- name    : SoficGroups.componentVertexMidrank_eq_sum_componentRankMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/224ace2b-6d54-4d5f-8513-0085eea80fce
-- title:
--   SoficGroups.componentVertexMidrank_eq_sum_componentRankMass
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

theorem SoficGroups.componentVertexMidrank_eq_sum_componentRankMass
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x =
      (∑ j ∈ (C.image b).filter (fun j => j < b x),
        componentRankMass C b j) + componentRankMass C b (b x) / 2 := by sorry
