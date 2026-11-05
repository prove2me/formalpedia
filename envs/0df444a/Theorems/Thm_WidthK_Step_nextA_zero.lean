-- Prove2me | Theorems.Thm_WidthK_Step_nextA_zero
-- name    : WidthK.Step.nextA_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:39:36.912621+00:00
-- url     : https://prove2.me/theorems/eeebe307-cc20-4c77-acb7-b9d55390869a
-- title:
--   Step: next A zero
-- statement:
--   The count at size 0 does not change.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L329-L330
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L329-L330

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

theorem WidthK.Step.nextA_zero (a : ℕ → ℕ) {r : ℕ} (hr : 0 < r) (c : ℕ) : nextA a r c 0 = a 0 := by sorry
