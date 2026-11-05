-- Prove2me | Theorems.Thm_UniformInK_Step_card_over_le
-- name    : UniformInK.Step.card_over_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:53.413186+00:00
-- url     : https://prove2.me/theorems/b63f2459-6b5b-4770-adbb-9d4d40f55c83
-- title:
--   Step: card over le
-- statement:
--   Below the size j of the rule every nonempty set Y of at most r literals lies in at most θ(r−|Y|)
--   clauses of size r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L143-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L143-L150

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
import Theorems.Thm_WidthK_Step_card_over_le
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

theorem UniformInK.Step.card_over_le (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) {r : ℕ} (hr : r < j) {Y : Finset α} (hY : Y.Nonempty) (hYr : Y.card ≤ r) :
    (Sparsify.over F r Y).card ≤ θ (r - Y.card) := by sorry
