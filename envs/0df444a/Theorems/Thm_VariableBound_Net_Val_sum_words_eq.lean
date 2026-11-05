-- Prove2me | Theorems.Thm_VariableBound_Net_Val_sum_words_eq
-- name    : VariableBound.Net.Val.sum_words_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:12.465793+00:00
-- url     : https://prove2.me/theorems/ed866df2-374a-4fb3-97e3-c35915ed7583
-- title:
--   Val: sum words eq
-- statement:
--   The sum over all labels of length c of «A is the label and B is the label».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L212-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L212-L230

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

theorem VariableBound.Net.Val.sum_words_eq (c : ℕ) (A B : List Bool) :
    ∑ θ ∈ words c, (if (A == θ) = true then (1 : ℤ) else 0) * (if (B == θ) = true then 1 else 0) =
      if A = B ∧ A.length = c then 1 else 0 := by sorry
