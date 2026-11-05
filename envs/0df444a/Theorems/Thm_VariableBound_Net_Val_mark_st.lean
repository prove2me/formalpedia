-- Prove2me | Theorems.Thm_VariableBound_Net_Val_mark_st
-- name    : VariableBound.Net.Val.mark_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:58.247794+00:00
-- url     : https://prove2.me/theorems/85cee429-a006-4667-bcbf-70c760030700
-- title:
--   Val: mark st
-- statement:
--   The setting of (σ, P) at the node a marks an object e that touches a iff e is a member of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L125-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L125-L130

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

theorem VariableBound.Net.Val.mark_st (σ : ℕ → Bool) (P : Finset ℕ) {a e : ℕ} (h : e ∈ tch g n D a) :
    mark g n D a (st g n D σ P a) e = decide (e ∈ P) := by sorry
