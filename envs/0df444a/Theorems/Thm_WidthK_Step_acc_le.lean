-- Prove2me | Theorems.Thm_WidthK_Step_acc_le
-- name    : WidthK.Step.acc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:25.4254+00:00
-- url     : https://prove2.me/theorems/1f96afa9-4ea8-42ed-a11a-eb2921a57aa3
-- title:
--   Step: acc le
-- statement:
--   At most β i · n clauses of size i are added along a path. U: the at most 2n literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L380-L399
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L380-L399

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
variable {n : ℕ} {U : Finset α} {β : ℕ → ℕ}

theorem WidthK.Step.acc_le {d : ℕ → ℕ} {N : Finset (Finset α)} {a : ℕ → ℕ} (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U)
    (h : InvK d F N a) (ha0 : a 0 = 0) (hβ : ∀ i, 0 < i → d i * (2 + ∑ i' ∈ range i, β i') ≤ β i) (i : ℕ) :
    a i ≤ β i * n := by sorry
