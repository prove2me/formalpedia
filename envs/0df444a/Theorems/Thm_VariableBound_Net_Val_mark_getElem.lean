-- Prove2me | Theorems.Thm_VariableBound_Net_Val_mark_getElem
-- name    : VariableBound.Net.Val.mark_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:05.83109+00:00
-- url     : https://prove2.me/theorems/e5e67ea7-92e9-439f-85a4-ea8d616ec503
-- title:
--   Val: mark get Elem
-- statement:
--   The mark of the object number t in the list of the objects that touch a is the bit number ⌈n/g⌉ +
--   t of the setting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L511-L514
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L511-L514

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_VariableBound_Net_Val
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.mark_getElem (a : ℕ) (z : List Bool) {t : ℕ} (h : t < (tch g n D a).length) :
    mark g n D a z (tch g n D a)[t] = z.getD (qv g n + t) false := by sorry
