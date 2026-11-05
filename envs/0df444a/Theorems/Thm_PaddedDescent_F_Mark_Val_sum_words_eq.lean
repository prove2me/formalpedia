-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_sum_words_eq
-- name    : PaddedDescent.F.Mark.Val.sum_words_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:19.849584+00:00
-- url     : https://prove2.me/theorems/211d5252-3ae8-4d0d-adfc-d01b2caee256
-- title:
--   Val: sum words eq
-- statement:
--   The sum over all labels of length c of «A is the label and B is the label».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L211-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L211-L229

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

theorem PaddedDescent.F.Mark.Val.sum_words_eq (c : ℕ) (A B : List Bool) :
    ∑ θ ∈ words c, (if (A == θ) = true then (1 : ℤ) else 0) * (if (B == θ) = true then 1 else 0) =
      if A = B ∧ A.length = c then 1 else 0 := by sorry
