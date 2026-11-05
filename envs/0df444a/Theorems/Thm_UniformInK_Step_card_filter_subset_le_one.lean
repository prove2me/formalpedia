-- Prove2me | Theorems.Thm_UniformInK_Step_card_filter_subset_le_one
-- name    : UniformInK.Step.card_filter_subset_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:47.735773+00:00
-- url     : https://prove2.me/theorems/e0eb4c92-05f8-40f6-93d1-5836a3dcdb30
-- title:
--   Step: card filter subset le one
-- statement:
--   A set of r elements lies in at most one set of r elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L133-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L133-L139

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
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

theorem UniformInK.Step.card_filter_subset_le_one {G : Finset (Finset α)} {r : ℕ} (hG : ∀ C ∈ G, C.card = r) {Y : Finset α} (hY : Y.card = r) :
    (G.filter fun C => Y ⊆ C).card ≤ 1 := by sorry
