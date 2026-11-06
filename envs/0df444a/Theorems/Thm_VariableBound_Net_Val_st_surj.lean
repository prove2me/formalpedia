-- Prove2me | Theorems.Thm_VariableBound_Net_Val_st_surj
-- name    : VariableBound.Net.Val.st_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:24.732907+00:00
-- url     : https://prove2.me/theorems/f9557d9a-5dbd-4b11-bb8c-1eda0eaf2fc9
-- title:
--   Val: st surj
-- statement:
--   Every good family of settings of the right lengths is the family of the settings of some (σ, P),
--   and σ violates the clauses of all members of P: «all literals of a marked clause are false, so Π₀ ⊆
--   V(ξ) and Π_j ⊆ V_j(ξ)». Needs g > 0 and well-formed data (WfD).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L519-L570
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L519-L570

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

theorem VariableBound.Net.Val.st_surj (hg : 0 < g) (hw : WfD k n D) {z : Fin g → List Bool}
    (hlen : ∀ a, (z a).length = qv g n + (tch g n D a).length) (hz : Gd g n D z) :
    ∃ (σ : Fin n → Bool) (P : Finset ℕ), P ⊆ vset (ext σ) D ∧ (fun a : Fin g => st g n D (ext σ) P a) = z := by sorry
