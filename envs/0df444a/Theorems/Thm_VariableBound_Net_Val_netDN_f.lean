-- Prove2me | Theorems.Thm_VariableBound_Net_Val_netDN_f
-- name    : VariableBound.Net.Val.netDN_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:20.465194+00:00
-- url     : https://prove2.me/theorems/caeeedc2-4679-4a43-b874-859048a28553
-- title:
--   Val: net DN f
-- statement:
--   The factor f_(a,a')(z, θ) of the network of the profile y is 1 if θ is the label that z shows to
--   a', and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L185-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L185-L187

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

theorem VariableBound.Net.Val.netDN_f (a a' : Fin g) (z θ : List Bool) :
    (netDN g (ctx g n D y fl)).f a a' z θ = if (labD g n D y a a' z == θ) = true then 1 else 0 := by sorry
