-- Prove2me | Theorems.Thm_VariableBound_Net_Val_prof_iff
-- name    : VariableBound.Net.Val.prof_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:50.962619+00:00
-- url     : https://prove2.me/theorems/7e294aaa-3f79-4773-b21b-b5a59bb9d7c0
-- title:
--   Val: prof iff
-- statement:
--   What `prof` says: for both kinds i, the node a owns μ_(a,i) marked objects, and for every other
--   node a' < g the string of the marks of the objects with the test {a, a'} has μ_(a,a',i) ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L164-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L164-L175

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
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.prof_iff {a : ℕ} {z : List Bool} : prof g n D y a z = true ↔
    (∀ i < 2, ownC g n D a i z = mu g D y a a i) ∧
      ∀ a' < g, a' ≠ a → ∀ i < 2, (str g n D a a' i z).count true = mu g D y a a' i := by sorry
