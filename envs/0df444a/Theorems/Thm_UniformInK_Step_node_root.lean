-- Prove2me | Theorems.Thm_UniformInK_Step_node_root
-- name    : UniformInK.Step.node_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:41:34.566379+00:00
-- url     : https://prove2.me/theorems/6408cb29-93aa-424b-9e2e-333f7eb21b5f
-- title:
--   Step: node root
-- statement:
--   The root of the tree of φ is a node with both counters 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L213-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L213-L215

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_node_root
import Theorems.Thm_WidthK_node_root
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}

theorem UniformInK.Step.node_root (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)) : NodeU θ k τ φ (Sparsify.red φ) 0 0 := by sorry
