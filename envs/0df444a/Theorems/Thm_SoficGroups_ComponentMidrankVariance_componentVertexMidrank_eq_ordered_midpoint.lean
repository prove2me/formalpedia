-- Prove2me | Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_eq_ordered_midpoint
-- name    : SoficGroups.ComponentMidrankVariance.componentVertexMidrank_eq_ordered_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/013c050e-77e6-4eec-a3d1-a9a5752e5944
-- title:
--   SoficGroups.ComponentMidrankVariance.componentVertexMidrank_eq_ordered_midpoint
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
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators

theorem SoficGroups.ComponentMidrankVariance.componentVertexMidrank_eq_ordered_midpoint
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    SoficGroups.componentVertexMidrank C b x =
      lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) (b x) +
        SoficGroups.componentRankMass C b (b x) / 2 := by sorry
