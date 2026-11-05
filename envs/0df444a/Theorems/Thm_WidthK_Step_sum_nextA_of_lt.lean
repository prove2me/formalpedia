-- Prove2me | Theorems.Thm_WidthK_Step_sum_nextA_of_lt
-- name    : WidthK.Step.sum_nextA_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:47.381857+00:00
-- url     : https://prove2.me/theorems/ca4c68ea-16d7-49b1-9c61-323280ee4eb7
-- title:
--   Step: sum next A of lt
-- statement:
--   The counts below size i grow by c in total if r < i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L120-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L120-L122

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

theorem WidthK.Step.sum_nextA_of_lt (a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : r < i) :
    ∑ i' ∈ range i, nextA a r c i' = ∑ i' ∈ range i, a i' + c := by sorry
