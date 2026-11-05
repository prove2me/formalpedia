-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_mark_eq
-- name    : PaddedDescent.F.Mark.Val.mark_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:58.921199+00:00
-- url     : https://prove2.me/theorems/e20eeac9-2258-4d43-af4c-95023603be54
-- title:
--   Val: mark eq
-- statement:
--   In a good state all marks of a clause agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L481-L503
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L481-L503

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

theorem PaddedDescent.F.Mark.Val.mark_eq {z : Fin g → List Bool} (hz : Gd g n Ls z) {e : ℕ} (he : e < (cls Ls).length) {a a' : Fin g}
    (ha : tchB g n Ls a e = true) (ha' : tchB g n Ls a' e = true) : mark g n Ls a (z a) e = mark g n Ls a' (z a') e := by sorry
