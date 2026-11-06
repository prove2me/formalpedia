-- Prove2me | Theorems.Thm_VariableBound_Net_Val_sum_owner
-- name    : VariableBound.Net.Val.sum_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:13.661108+00:00
-- url     : https://prove2.me/theorems/301ac4b3-dd9c-4579-b5c8-86fe38b6c00e
-- title:
--   Val: sum owner
-- statement:
--   Counting the members of P with a property p owner by owner counts each once, if g > 0, the data
--   are well formed (WfD) and P is a set of places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L340-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L340-L354

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.sum_owner (hg : 0 < g) (hW : WfD k n D) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ Finset.range g, (P.filter fun e => p e ∧ ownB g n D e a = true).card = (P.filter p).card := by sorry
