-- Prove2me | Theorems.Thm_VariableBound_Net_Val_getD_st_ge
-- name    : VariableBound.Net.Val.getD_st_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:00.033094+00:00
-- url     : https://prove2.me/theorems/a3f62722-5f0c-4210-9897-87d26c7d196a
-- title:
--   Val: get D st ge
-- statement:
--   The mark bit number t of the setting of (σ, P) at a says whether the object number t in the list
--   of the objects that touch a is a member of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L503-L507
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L503-L507

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

theorem VariableBound.Net.Val.getD_st_ge (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {t : ℕ} (h : t < (tch g n D a).length) :
    (st g n D σ P a).getD (qv g n + t) false = decide ((tch g n D a)[t] ∈ P) := by sorry
