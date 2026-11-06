-- Prove2me | Theorems.Thm_VariableBound_Net_Val_prof_st_iff
-- name    : VariableBound.Net.Val.prof_st_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:19.746316+00:00
-- url     : https://prove2.me/theorems/2a1e6b72-aefd-4bf9-a888-cbc0c507da67
-- title:
--   Val: prof st iff
-- statement:
--   For a set P of places of objects: the settings of (σ, P) at all nodes have the numbers of the
--   profile y exactly if P belongs to y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L310-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L310-L317

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

theorem VariableBound.Net.Val.prof_st_iff (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) :
    (∀ a : Fin g, prof g n D y a (st g n D σ P a) = true) ↔ Match g n D y P := by sorry
