-- Prove2me | Theorems.Thm_VariableBound_Net_Val_mark_eq
-- name    : VariableBound.Net.Val.mark_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:55.450792+00:00
-- url     : https://prove2.me/theorems/5ff30d51-cd91-454a-bebf-02f5f4040ca0
-- title:
--   Val: mark eq
-- statement:
--   «In a nonzero term the marks of an object agree at all nodes that it touches, because its tests
--   form a path»: in a good family z of settings, an object e has the same mark at any two nodes that it
--   touches.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L470-L492
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L470-L492

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

theorem VariableBound.Net.Val.mark_eq {z : Fin g → List Bool} (hz : Gd g n D z) {e : ℕ} (he : e < (objs D).length) {a a' : Fin g}
    (ha : tchB g n D a e = true) (ha' : tchB g n D a' e = true) : mark g n D a (z a) e = mark g n D a' (z a') e := by sorry
