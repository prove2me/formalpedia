-- Prove2me | Theorems.Thm_VariableBound_Net_Val_sum_good
-- name    : VariableBound.Net.Val.sum_good
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:39.834057+00:00
-- url     : https://prove2.me/theorems/32ae41c1-6996-48bb-ae28-c7b88298f04f
-- title:
--   Val: sum good
-- statement:
--   A sum over the good families of settings is a sum over the pairs (σ, P) of an assignment and a
--   set of objects whose clauses it violates, if g > 0 and the data are well formed (WfD).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L574-L595
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L574-L595

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

theorem VariableBound.Net.Val.sum_good (hg : 0 < g) (hw : WfD k n D) (F : (Fin g → List Bool) → ℤ) :
    (∑ z ∈ Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n D a).length),
      by classical exact if Gd g n D z then F z else 0) =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) D).powerset, F fun a => st g n D (ext σ) P a := by sorry
