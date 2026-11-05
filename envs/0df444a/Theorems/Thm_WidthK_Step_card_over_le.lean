-- Prove2me | Theorems.Thm_WidthK_Step_card_over_le
-- name    : WidthK.Step.card_over_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:38.512222+00:00
-- url     : https://prove2.me/theorems/c91306c9-5ba4-424d-a8f4-5277d344bbc0
-- title:
--   Step: card over le
-- statement:
--   Below the size j of the rule every literal lies in at most θ s clauses of size s + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L213-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L213-L222

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
open WidthK.Step

theorem WidthK.Step.card_over_le (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) {s : ℕ} (hs : s + 1 < j) (y : α) :
    (Sparsify.over F (s + 1) {y}).card ≤ θ s := by sorry
