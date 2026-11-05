-- Prove2me | Theorems.Thm_UniformInK_Bound_bound
-- name    : UniformInK.Bound.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:38:33.177007+00:00
-- url     : https://prove2.me/theorems/19cc0f3e-ca66-4f7e-9448-884cf1bb3949
-- title:
--   Bound: bound
-- statement:
--   A path has at most (β 0 + … + β (k-1)) · n steps, and the count t of `NodeU`, in which each
--   heavy step counts τ units, is at most k · n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L75-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L75-L101

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

theorem UniformInK.Bound.bound (hT : ThrU k τ θ β) (hU : U.card ≤ 2 * n) (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n := by sorry
