-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_length_mlab
-- name    : PaddedDescent.F.Mark.Val.length_mlab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:17.912947+00:00
-- url     : https://prove2.me/theorems/740c4e87-e1bc-47c7-b5f4-bb7495b8e33a
-- title:
--   Val: length mlab
-- statement:
--   The label that a state with the profile writes has the prescribed length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L235-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L235-L240

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

theorem PaddedDescent.F.Mark.Val.length_mlab (hLen : StEncLen) (h0 : 0 < b) {a a' : ℕ} (ha' : a' < g) (hne : a' ≠ a) {z : List Bool}
    (hz : prof g n Ls y a z = true) : (mlab g n β b Ls a a' z).length = mcap g n β b Ls y a a' := by sorry
