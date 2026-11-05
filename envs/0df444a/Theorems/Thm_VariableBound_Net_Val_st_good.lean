-- Prove2me | Theorems.Thm_VariableBound_Net_Val_st_good
-- name    : VariableBound.Net.Val.st_good
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:22.207613+00:00
-- url     : https://prove2.me/theorems/34c44cd0-f68b-4321-9bde-8d64e48e843a
-- title:
--   Val: st good
-- statement:
--   The settings of (σ, P) are good if g > 0, the data are well formed (WfD), σ is false at all
--   numbers ≥ n, and σ violates the clauses of all members of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L419-L436
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L419-L436

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.st_good (hg : 0 < g) (hw : WfD k n D) {σ : ℕ → Bool} (hσ : ∀ x, n ≤ x → σ x = false) {P : Finset ℕ}
    (hP : P ⊆ vset σ D) : Gd g n D fun a => st g n D σ P a := by sorry
