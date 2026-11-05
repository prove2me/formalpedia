-- Prove2me | Theorems.Thm_WidthK_Step_card_filter_mem_le_one
-- name    : WidthK.Step.card_filter_mem_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:49.558341+00:00
-- url     : https://prove2.me/theorems/fb17a6d7-623c-4edd-8359-cc14c206804d
-- title:
--   Step: card filter mem le one
-- statement:
--   A literal lies in at most one set of size 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L201-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L201-L210

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
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
open WidthK.Step

theorem WidthK.Step.card_filter_mem_le_one {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) :
    (G.filter fun C => y ∈ C).card ≤ 1 := by sorry
