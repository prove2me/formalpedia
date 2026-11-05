-- Prove2me | Theorems.Thm_UniformInK_Step_node_heavy
-- name    : UniformInK.Step.node_heavy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:44.568492+00:00
-- url     : https://prove2.me/theorems/b1d18ec1-d32d-4a97-9a78-663f8dbe4fe4
-- title:
--   Step: node heavy
-- statement:
--   The heavy child counts one more step and adds τ to t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L229-L251
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L229-L251

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
import Theorems.Thm_WidthK_Node_heavy
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

theorem UniformInK.Step.node_heavy (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (heavy F j H) (p + 1) (t + τ) := by sorry
