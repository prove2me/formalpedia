-- Prove2me | Theorems.Thm_VariableBound_Net_Val_prod_wz_st
-- name    : VariableBound.Net.Val.prod_wz_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:47.689538+00:00
-- url     : https://prove2.me/theorems/e7eda46c-a6bb-4824-a495-fba59e4a527b
-- title:
--   Val: prod wz st
-- statement:
--   The weights of the nodes at the settings of (σ, P) multiply to the value of the term of P in
--   display (65), if g > 0, the data are well formed (WfD) and P is a set of places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L359-L382
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L359-L382

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

theorem VariableBound.Net.Val.prod_wz_st (hg : 0 < g) (hw : WfD k n D) (σ : ℕ → Bool) {P : Finset ℕ}
    (hP : P ⊆ Finset.range (objs D).length) :
    ∏ a : Fin g, wz g n D fl a (st g n D σ P a) = wt D fl P := by sorry
