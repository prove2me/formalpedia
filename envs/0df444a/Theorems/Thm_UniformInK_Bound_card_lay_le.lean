-- Prove2me | Theorems.Thm_UniformInK_Bound_card_lay_le
-- name    : UniformInK.Bound.card_lay_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:51.928647+00:00
-- url     : https://prove2.me/theorems/b0272719-54bd-4cd5-bc82-b40ca37f7863
-- title:
--   Bound: card lay le
-- statement:
--   At most 4·θ(i−1)·n added clauses of size i ≥ 1 are still present. U: the at most 2n literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L36-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L36-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

theorem UniformInK.Bound.card_lay_le (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) {i : ℕ} (hi : 0 < i) :
    (lay N i).card ≤ 4 * θ (i - 1) * n := by sorry
