-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_vio_iff
-- name    : PaddedDescent.F.Mark.Val.vio_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:27.212296+00:00
-- url     : https://prove2.me/theorems/5bb97351-6ae7-4f52-b8a1-3927361577da
-- title:
--   Val: vio iff
-- statement:
--   The Val construction uses the vio iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L416-L417
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L416-L417

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

theorem PaddedDescent.F.Mark.Val.vio_iff {σ : ℕ → Bool} {C : Cl} : vio σ C = true ↔ ∀ l ∈ C, σ l.1 ≠ l.2 := by sorry
