-- Prove2me | Theorems.Thm_WidthK_InvK_step
-- name    : WidthK.InvK.step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:34:38.747566+00:00
-- url     : https://prove2.me/theorems/a201dd27-bd06-477b-856b-3e98beed1963
-- title:
--   Inv K: step
-- statement:
--   A step that adds A, all of size r, keeps the invariant: N becomes `nextN N A`, and the count at
--   size r grows by |A|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L152-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L152-L192

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
variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem WidthK.InvK.step (h : InvK d F N a) (hA : AddK d F A r) :
    InvK d (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) := by sorry
