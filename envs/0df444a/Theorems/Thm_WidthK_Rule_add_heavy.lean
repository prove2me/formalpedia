-- Prove2me | Theorems.Thm_WidthK_Rule_add_heavy
-- name    : WidthK.Rule.add_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:39:24.873194+00:00
-- url     : https://prove2.me/theorems/ac230c17-66e9-43fa-aa0b-6e84ff09a6de
-- title:
--   Rule: add heavy
-- statement:
--   The heavy child of the rule is a step that adds the petals, of size j - |H|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L272-L312
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L272-L312

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

theorem WidthK.Rule.add_heavy (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) :
    AddK (dg θ) F (petals F j H) (j - H.card) := by sorry
