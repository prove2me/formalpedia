-- Prove2me | Theorems.Thm_SoficGroups_boundary_permutationGraph_eq_commutationDefect
-- name    : SoficGroups.boundary_permutationGraph_eq_commutationDefect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/eb9f4a1b-7f11-41f2-8e6b-c6764df19822
-- title:
--   SoficGroups.boundary_permutationGraph_eq_commutationDefect
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
universe u₁ u₂ u₃

theorem SoficGroups.boundary_permutationGraph_eq_commutationDefect
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) :
    boundary (fun i => (σ i).prodCongr (σ i)) (permutationGraph p) =
      permutationCommutationDefect σ p := by sorry
