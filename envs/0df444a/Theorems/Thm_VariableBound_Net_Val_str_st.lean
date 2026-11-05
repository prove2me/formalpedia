-- Prove2me | Theorems.Thm_VariableBound_Net_Val_str_st
-- name    : VariableBound.Net.Val.str_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:59.173205+00:00
-- url     : https://prove2.me/theorems/6f6a199c-9fcc-47da-b2db-781a78c490b1
-- title:
--   Val: str st
-- statement:
--   The string of the marks that the setting of (σ, P) at a gives to the objects of kind i with the
--   test {a, a'}: the bit of an object says whether it is a member of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L263-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L263-L266

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.str_st (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    str g n D a a' i (st g n D σ P a) = (tst g n D a a' i).map fun e => decide (e ∈ P) := by sorry
