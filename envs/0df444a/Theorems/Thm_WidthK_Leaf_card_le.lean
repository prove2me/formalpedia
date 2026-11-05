-- Prove2me | Theorems.Thm_WidthK_Leaf_card_le
-- name    : WidthK.Leaf.card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:39.712226+00:00
-- url     : https://prove2.me/theorems/8bec255b-fcdc-407b-b3ac-e9d58f67b00f
-- title:
--   Leaf: card le
-- statement:
--   A leaf has at most 2n · (θ 0 + … + θ (k-1)) clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L439-L463
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L439-L463

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

theorem WidthK.Leaf.card_le (hθ : ∀ i, 0 < θ i) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : Leaf θ k F)
    (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) : F.card ≤ 2 * n * ∑ i ∈ range k, θ i := by sorry
