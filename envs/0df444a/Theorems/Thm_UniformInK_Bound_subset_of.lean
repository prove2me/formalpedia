-- Prove2me | Theorems.Thm_UniformInK_Bound_subset_of
-- name    : UniformInK.Bound.subset_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:09:29.093011+00:00
-- url     : https://prove2.me/theorems/9f7156b2-e0fc-4c78-b727-4bff64045a2a
-- title:
--   Bound: subset of
-- statement:
--   If the clauses of φ are subsets of U, so are the clauses of every node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L68-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

theorem UniformInK.Bound.subset_of (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) : ∀ C ∈ F, C ⊆ U := by sorry
