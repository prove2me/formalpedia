-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_st_good
-- name    : PaddedDescent.F.Mark.Val.st_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:55.735938+00:00
-- url     : https://prove2.me/theorems/a271d45e-6f91-49e8-878a-8b46a67cc4d1
-- title:
--   Val: st good
-- statement:
--   The states of (σ, P) are good if σ violates all clauses of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L435-L452
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L435-L452

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

theorem PaddedDescent.F.Mark.Val.st_good (hg : 0 < g) (hw : WfL k n Ls) {σ : ℕ → Bool} (hσ : ∀ x, n ≤ x → σ x = false) {P : Finset ℕ}
    (hP : P ⊆ vset σ Ls) : Gd g n Ls fun a => st g n Ls σ P a := by sorry
