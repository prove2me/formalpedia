-- Prove2me | Theorems.Thm_VariableBound_Net_Val_getD_st_lt
-- name    : VariableBound.Net.Val.getD_st_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:53:33.46721+00:00
-- url     : https://prove2.me/theorems/bbb83227-47ae-4d3d-b437-27d5d80a40dd
-- title:
--   Val: get D st lt
-- statement:
--   The value bit number r < ⌈n/g⌉ of the setting of the node a is the value of the variable a·⌈n/g⌉ +
--   r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L118-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L118-L122

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.getD_st_lt (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {r : ℕ} (h : r < qv g n) :
    (st g n D σ P a).getD r false = σ (a * qv g n + r) := by sorry
