-- Prove2me | Theorems.Thm_SparsificationLemma_Bound_bound
-- name    : SparsificationLemma.Bound.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:55:20.304519+00:00
-- url     : https://prove2.me/theorems/eb4bb60f-7501-42b7-b005-e50fdf9e4f0f
-- title:
--   Bound: bound
-- statement:
--   A path has at most (β 0 + … + β (k-1)) · n steps, and its steps of the second kind use at most
--   (k−1) · n units, τ each.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L68-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L68-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_UniformInK_Bound_bound
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK
open SparsificationLemma.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

theorem SparsificationLemma.Bound.bound (hT : ThrC k τ θ β) (hU : U.card ≤ 2 * n) (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ (k - 1) * n := by sorry
