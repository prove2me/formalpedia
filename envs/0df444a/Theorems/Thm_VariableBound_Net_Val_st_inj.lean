-- Prove2me | Theorems.Thm_VariableBound_Net_Val_st_inj
-- name    : VariableBound.Net.Val.st_inj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:19.708824+00:00
-- url     : https://prove2.me/theorems/82039378-7417-4d63-9987-d2ae6e73eeca
-- title:
--   Val: st inj
-- statement:
--   The settings determine σ and P: «each once». Needs g > 0, well-formed data (WfD), and that P and
--   P' are sets of places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L446-L465
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L446-L465

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

theorem VariableBound.Net.Val.st_inj (hg : 0 < g) (hw : WfD k n D) {σ σ' : Fin n → Bool} {P P' : Finset ℕ}
    (hP : P ⊆ Finset.range (objs D).length) (hP' : P' ⊆ Finset.range (objs D).length)
    (h : (fun a : Fin g => st g n D (ext σ) P a) = fun a : Fin g => st g n D (ext σ') P' a) : σ = σ' ∧ P = P' := by sorry
