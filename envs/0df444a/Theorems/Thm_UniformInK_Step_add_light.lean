-- Prove2me | Theorems.Thm_UniformInK_Step_add_light
-- name    : UniformInK.Step.add_light
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:41:54.115958+00:00
-- url     : https://prove2.me/theorems/f207c748-c719-45df-90f6-d5a5e7d2dd20
-- title:
--   Step: add light
-- statement:
--   The light child of the rule is a step that adds one set of size |H|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L153-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L153-L163

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
import Theorems.Thm_WidthK_Rule_add_light
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

theorem UniformInK.Step.add_light (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F {H} H.card := by sorry
