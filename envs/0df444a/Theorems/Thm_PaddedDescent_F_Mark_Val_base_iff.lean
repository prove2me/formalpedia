-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_base_iff
-- name    : PaddedDescent.F.Mark.Val.base_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:42:42.370778+00:00
-- url     : https://prove2.me/theorems/c604340c-6507-475f-93e3-62e2ec81fd65
-- title:
--   Val: base iff
-- statement:
--   The Val construction uses the base iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L409-L414
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L409-L414

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
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.base_iff {a : ℕ} {z : List Bool} : base g n Ls a z = true ↔
    (∀ r < qv g n, a * qv g n + r < n ∨ z.getD r false = false) ∧
      ∀ e ∈ tch g n Ls a, mark g n Ls a z e = false ∨
        ∀ l ∈ (clAt Ls e).2, l.1 / qv g n ≠ a ∨ z.getD (l.1 % qv g n) false ≠ l.2 := by sorry
