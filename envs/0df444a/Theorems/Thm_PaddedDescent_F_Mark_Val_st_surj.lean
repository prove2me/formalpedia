-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_st_surj
-- name    : PaddedDescent.F.Mark.Val.st_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:44.030199+00:00
-- url     : https://prove2.me/theorems/7481a192-a90d-47ac-9219-c8ec896ab6bd
-- title:
--   Val: st surj
-- statement:
--   Every good family of states is the family of the states of some (σ, P).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L524-L575
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L524-L575

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.st_surj (hg : 0 < g) (hw : WfL k n Ls) {z : Fin g → List Bool}
    (hlen : ∀ a, (z a).length = qv g n + (tch g n Ls a).length) (hz : Gd g n Ls z) :
    ∃ (σ : Fin n → Bool) (P : Finset ℕ), P ⊆ vset (ext σ) Ls ∧ (fun a : Fin g => st g n Ls (ext σ) P a) = z := by sorry
