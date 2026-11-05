-- Prove2me | Theorems.Thm_UniformInK_Step_card_lay_le
-- name    : UniformInK.Step.card_lay_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:41:45.801925+00:00
-- url     : https://prove2.me/theorems/4a6c33b3-cdc7-4d23-b4bc-bc333b04112d
-- title:
--   Step: card lay le
-- statement:
--   A step removes at most |A| · 2·θ(i−r) clauses of a size i ≥ r from N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L68-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L68-L82

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
import Theorems.Thm_WidthK_Step_card_lay_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem UniformInK.Step.card_lay_le (h : InvU θ F N a) (hA : AddU θ F A r) {i : ℕ} (hi : r ≤ i) :
    (lay N i).card ≤ ((lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C).card + A.card * (2 * θ (i - r)) := by sorry
