-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_sum_good
-- name    : PaddedDescent.F.Mark.Val.sum_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:50.026615+00:00
-- url     : https://prove2.me/theorems/b688d5d0-02c0-4df9-9a20-f9dcf4197807
-- title:
--   Val: sum good
-- statement:
--   A sum over the good states is a sum over the pairs (σ, P).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L578-L599
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L578-L599

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

theorem PaddedDescent.F.Mark.Val.sum_good (hg : 0 < g) (hw : WfL k n Ls) (F : (Fin g → List Bool) → ℤ) :
    (∑ z ∈ Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n Ls a).length),
      by classical exact if Gd g n Ls z then F z else 0) =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) Ls).powerset, F fun a => st g n Ls (ext σ) P a := by sorry
