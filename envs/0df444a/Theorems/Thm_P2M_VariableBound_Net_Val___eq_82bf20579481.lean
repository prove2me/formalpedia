-- Prove2me | Theorems.Thm_P2M_VariableBound_Net_Val___eq_82bf20579481
-- name    : P2M_VariableBound_Net_Val___eq_82bf20579481
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:47.080126+00:00
-- url     : https://prove2.me/theorems/322305de-4611-4c88-ab1f-699d2cd9417e
-- title:
--   P2 M Variable Bound Net Val   eq 82bf20579481: P2 M Variable Bound Net Val   eq 82bf20579481
-- statement:
--   Ψ_(a,a') for two different nodes whose settings z, z' belong to the profile y: 1 if they give
--   the same mark to every object with the test {a, a'}, and 0 otherwise. Needs that the labels
--   determine the strings (StLab).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L235-L247
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L235-L247

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

theorem P2M_VariableBound_Net_Val___eq_82bf20579481 (hL : StLab) {a a' : Fin g} (hne : a ≠ a') {z z' : List Bool}
    (hz : prof g n D y a z = true) (hz' : prof g n D y a' z' = true) :
    (netDN g (ctx g n D y fl)).Ψ a a' z z' =
      if ∀ i < (2 : ℕ), str g n D a a' i z = str g n D a' a i z' then 1 else 0 := by sorry

alias «VariableBound».«Net».«Val».«Ψ_eq» := P2M_VariableBound_Net_Val___eq_82bf20579481
