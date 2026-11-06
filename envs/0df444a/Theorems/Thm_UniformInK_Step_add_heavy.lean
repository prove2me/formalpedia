-- Prove2me | Theorems.Thm_UniformInK_Step_add_heavy
-- name    : UniformInK.Step.add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:41:56.085141+00:00
-- url     : https://prove2.me/theorems/02649e28-a71b-427b-970a-0beb737b07ae
-- title:
--   Step: add heavy
-- statement:
--   The heavy child of the rule is a step that adds the petals, of size j − |H|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L166-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L166-L198

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
import Theorems.Thm_WidthK_Rule_add_heavy
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

theorem UniformInK.Step.add_heavy (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F (petals F j H) (j - H.card) := by sorry
