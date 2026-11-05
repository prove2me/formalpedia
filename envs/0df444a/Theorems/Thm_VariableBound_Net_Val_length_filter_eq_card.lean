-- Prove2me | Theorems.Thm_VariableBound_Net_Val_length_filter_eq_card
-- name    : VariableBound.Net.Val.length_filter_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:03.018546+00:00
-- url     : https://prove2.me/theorems/c2b3d566-b2be-4fe2-b011-f25c1992930c
-- title:
--   Val: length filter eq card
-- statement:
--   The length of a filtered list without repetitions is the number of elements of the set that it
--   lists.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L253-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L253-L259

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

theorem VariableBound.Net.Val.length_filter_eq_card {l : List ℕ} (hl : l.Nodup) (p : ℕ → Bool) (S : Finset ℕ) (h : ∀ e, (e ∈ l ∧ p e = true) ↔ e ∈ S) :
    (l.filter p).length = S.card := by sorry
