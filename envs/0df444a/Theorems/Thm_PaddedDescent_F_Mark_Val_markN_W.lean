-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_markN_W
-- name    : PaddedDescent.F.Mark.Val.markN_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:53.152261+00:00
-- url     : https://prove2.me/theorems/faa76963-fa46-4006-9118-6201142993da
-- title:
--   Val: mark N W
-- statement:
--   The Val construction uses the mark N W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L186-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L186-L187

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

theorem PaddedDescent.F.Mark.Val.markN_W (a : Fin g) (z : List Bool) : (markN g (ctx g n β b Ls y)).W a z = mW g n Ls y a z := by sorry
