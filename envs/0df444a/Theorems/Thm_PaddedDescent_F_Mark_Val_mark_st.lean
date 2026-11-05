-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_mark_st
-- name    : PaddedDescent.F.Mark.Val.mark_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:41.600606+00:00
-- url     : https://prove2.me/theorems/2ba2f8ff-53b5-4807-bc8e-a3668c0b5113
-- title:
--   Val: mark st
-- statement:
--   The Val construction uses the mark st property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L132-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L132-L137

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

theorem PaddedDescent.F.Mark.Val.mark_st (σ : ℕ → Bool) (P : Finset ℕ) {a e : ℕ} (h : e ∈ tch g n Ls a) :
    mark g n Ls a (st g n Ls σ P a) e = decide (e ∈ P) := by sorry
