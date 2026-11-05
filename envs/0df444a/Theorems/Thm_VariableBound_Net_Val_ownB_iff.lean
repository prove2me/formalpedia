-- Prove2me | Theorems.Thm_VariableBound_Net_Val_ownB_iff
-- name    : VariableBound.Net.Val.ownB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:52:52.053918+00:00
-- url     : https://prove2.me/theorems/ae3f5044-00aa-4a1e-9cd2-f388084a9b9e
-- title:
--   Val: own B iff
-- statement:
--   The node a owns the object e iff e touches a and no smaller node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L70-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L70-L82

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_ownB_iff

set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.ownB_iff {e a : ℕ} : ownB g n D e a = true ↔ tchB g n D a e = true ∧ ∀ c < g, c < a → tchB g n D c e = false := by sorry
