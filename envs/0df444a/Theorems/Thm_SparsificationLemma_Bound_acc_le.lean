-- Prove2me | Theorems.Thm_SparsificationLemma_Bound_acc_le
-- name    : SparsificationLemma.Bound.acc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:52.679081+00:00
-- url     : https://prove2.me/theorems/629fb027-abd7-4bc4-b1e7-e19ca89c6188
-- title:
--   Bound: acc le
-- statement:
--   At most β i · n clauses of size i < k are added along a path.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L42-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L42-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_UniformInK_Bound_acc_le
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK
open SparsificationLemma.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

theorem SparsificationLemma.Bound.acc_le (hT : ThrC k τ θ β) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) (ha0 : a 0 = 0) (i : ℕ) (hik : i < k) :
    a i ≤ β i * n := by sorry
