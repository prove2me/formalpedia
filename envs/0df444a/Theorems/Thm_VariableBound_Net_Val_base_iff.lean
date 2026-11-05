-- Prove2me | Theorems.Thm_VariableBound_Net_Val_base_iff
-- name    : VariableBound.Net.Val.base_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:59:40.399116+00:00
-- url     : https://prove2.me/theorems/bf30c326-c849-4aef-8c41-2712496e7a8a
-- title:
--   Val: base iff
-- statement:
--   What `base` says: a value bit of a variable with a number ≥ n is 0, and every object that
--   touches a is unmarked or has all its literals at a false.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L388-L393
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L388-L393

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

theorem VariableBound.Net.Val.base_iff {a : ℕ} {z : List Bool} : base g n D a z = true ↔
    (∀ r < qv g n, a * qv g n + r < n ∨ z.getD r false = false) ∧
      ∀ e ∈ tch g n D a, mark g n D a z e = false ∨
        ∀ l ∈ (clOf D e), l.1 / qv g n ≠ a ∨ z.getD (l.1 % qv g n) false ≠ l.2 := by sorry
