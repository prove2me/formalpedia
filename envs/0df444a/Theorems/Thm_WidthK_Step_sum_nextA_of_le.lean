-- Prove2me | Theorems.Thm_WidthK_Step_sum_nextA_of_le
-- name    : WidthK.Step.sum_nextA_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:27.653957+00:00
-- url     : https://prove2.me/theorems/7748349c-6be3-46d2-b265-f55e64d9c7e3
-- title:
--   Step: sum next A of le
-- statement:
--   The counts below size i do not change if i ≤ r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L113-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L113-L117

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
open WidthK.Step
variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem WidthK.Step.sum_nextA_of_le (a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : i ≤ r) :
    ∑ i' ∈ range i, nextA a r c i' = ∑ i' ∈ range i, a i' := by sorry
