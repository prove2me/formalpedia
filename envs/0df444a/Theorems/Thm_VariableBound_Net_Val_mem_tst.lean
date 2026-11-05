-- Prove2me | Theorems.Thm_VariableBound_Net_Val_mem_tst
-- name    : VariableBound.Net.Val.mem_tst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:39.206275+00:00
-- url     : https://prove2.me/theorems/61336886-343c-4357-8684-5c0c588d0de3
-- title:
--   Val: mem tst
-- statement:
--   The list `tst g n D a b i` holds the places of the objects of kind i with the test {a, b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L85-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L85-L87

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.mem_tst {a b i e : ℕ} : e ∈ tst g n D a b i ↔
    e < (objs D).length ∧ (obAt D e).1 = i ∧ linkB g n D e (min a b) (max a b) = true := by sorry
