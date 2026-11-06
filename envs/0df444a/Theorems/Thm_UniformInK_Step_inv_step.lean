-- Prove2me | Theorems.Thm_UniformInK_Step_inv_step
-- name    : UniformInK.Step.inv_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:48.381891+00:00
-- url     : https://prove2.me/theorems/ce3e5458-1384-4078-8480-b520be95a6ea
-- title:
--   Step: inv step
-- statement:
--   A step that adds A, all of size r, keeps the invariant: N becomes nextN N A, and the count at
--   size r grows by |A|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L86-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L86-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem UniformInK.Step.inv_step (h : InvU θ F N a) (hA : AddU θ F A r) :
    InvU θ (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) := by sorry
