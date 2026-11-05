-- Prove2me | Theorems.Thm_UniformInK_Step_sub_add
-- name    : UniformInK.Step.sub_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:54.470858+00:00
-- url     : https://prove2.me/theorems/639fe7e8-bcfa-433b-917e-35aecb19f5c7
-- title:
--   Step: sub add
-- statement:
--   After a step every clause is still a subset of a clause of φ, nonempty if that one is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L203-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L203-L210

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
import Theorems.Thm_WidthK_Step_sub_add
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

theorem UniformInK.Step.sub_add {A : Finset (Finset α)} {r : ℕ} (h : ∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) (hA : AddU θ F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by sorry
