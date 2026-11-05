-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_linkB_iff
-- name    : PaddedDescent.F.Mark.Val.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:42:00.328259+00:00
-- url     : https://prove2.me/theorems/ceabc22e-ab15-48b6-b5b3-31cea1441587
-- title:
--   Val: link B iff
-- statement:
--   The Val construction uses the link B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L66-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L66-L83

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
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.linkB_iff {e a b : ℕ} : linkB g n Ls e a b = true ↔
    a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧ ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by sorry
