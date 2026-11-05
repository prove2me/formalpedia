-- Prove2me | Theorems.Thm_UniformInK_Step_node_light
-- name    : UniformInK.Step.node_light
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:12.023852+00:00
-- url     : https://prove2.me/theorems/0a2d3a0d-d7ae-4720-95d2-57a52f5c256b
-- title:
--   Step: node light
-- statement:
--   The light child counts one more step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L218-L226
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L218-L226

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
import Theorems.Thm_WidthK_Node_light
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

theorem UniformInK.Step.node_light (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (light F H) (p + 1) t := by sorry
