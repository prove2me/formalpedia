-- Prove2me | Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_variance_eq
-- name    : SoficGroups.ComponentMidrankVariance.componentVertexMidrank_variance_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/45572643-cdef-433b-8116-2adbf02d4c3d
-- title:
--   SoficGroups.ComponentMidrankVariance.componentVertexMidrank_variance_eq
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

theorem SoficGroups.ComponentMidrankVariance.componentVertexMidrank_variance_eq
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C,
      (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
      (C.card : ℝ) *
        SoficGroups.midrankVariance (SoficGroups.componentRankMassList C b) := by sorry
