-- Prove2me | Theorems.Thm_WidthK_Node_subset_of
-- name    : WidthK.Node.subset_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:42.184467+00:00
-- url     : https://prove2.me/theorems/4052b612-6304-4268-b07f-7038c737dd34
-- title:
--   Node: subset of
-- statement:
--   If the clauses of φ are subsets of U, so are the clauses of every node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L402-L405
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L402-L405

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
variable {n : ℕ} {U : Finset α} {β : ℕ → ℕ}

theorem WidthK.Node.subset_of (hφ : ∀ C ∈ φ, C ⊆ U) (h : Node θ k τ φ F p t) : ∀ C ∈ F, C ⊆ U := by sorry
