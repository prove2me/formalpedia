-- Prove2me | Theorems.Thm_VariableBound_Net_Val_ownC_st
-- name    : VariableBound.Net.Val.ownC_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:59:15.858321+00:00
-- url     : https://prove2.me/theorems/1438bd2f-ed49-4eb8-81bc-3889d2a750cc
-- title:
--   Val: own C st
-- statement:
--   In the setting of (σ, P), for a set P of places of objects, the number of marked objects of kind
--   i that a owns is the number of members of P of kind i that a owns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L277-L289
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L277-L289

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

theorem VariableBound.Net.Val.ownC_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (a i : ℕ) :
    ownC g n D a i (st g n D σ P a) = oc g n D P a i := by sorry
