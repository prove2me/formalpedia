-- Prove2me | Theorems.Thm_WidthK_Step_sub_add
-- name    : WidthK.Step.sub_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:55.052263+00:00
-- url     : https://prove2.me/theorems/fcd2435f-6e55-42af-8846-764cff99476a
-- title:
--   Step: sub add
-- statement:
--   After a step every clause is still a subset of a clause of φ, nonempty if that one is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L319-L326
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L319-L326

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
variable {τ p t : ℕ} {φ : Finset (Finset α)}
open WidthK.Step

theorem WidthK.Step.sub_add {d : ℕ → ℕ} {A : Finset (Finset α)} {r : ℕ} (h : Node θ k τ φ F p t) (hA : AddK d F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by sorry
