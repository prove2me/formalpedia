-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_prod_sign_st
-- name    : PaddedDescent.F.Mark.Val.prod_sign_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:33.172801+00:00
-- url     : https://prove2.me/theorems/0bbd715d-b077-432f-9aec-f00ce92ccffc
-- title:
--   Val: prod sign st
-- statement:
--   The signs of the nodes at the states of (σ, P) multiply to the sign of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L398-L405
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L398-L405

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.prod_sign_st (hg : 0 < g) (hw : WfL k n Ls) (σ : ℕ → Bool) {P : Finset ℕ}
    (hP : P ⊆ Finset.range (cls Ls).length) :
    ∏ a : Fin g, (-1 : ℤ) ^ sgE g n Ls a (st g n Ls σ P a) = sgnP Ls P := by sorry
