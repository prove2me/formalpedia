-- Prove2me | Theorems.Thm_WidthK_node_root
-- name    : WidthK.node_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:58.623094+00:00
-- url     : https://prove2.me/theorems/3c86a4bd-02d5-49c6-a888-a85e89be6e75
-- title:
--   Width K: node root
-- statement:
--   The root of the tree of φ is a node with both counters 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L335-L337
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L335-L337

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
import Theorems.Thm_Groundwork_Sparsify_node_root
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}

theorem WidthK.node_root (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)) : Node θ k τ φ (Sparsify.red φ) 0 0 := by sorry
