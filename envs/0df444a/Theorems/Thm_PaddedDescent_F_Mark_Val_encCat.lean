-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_encCat
-- name    : PaddedDescent.F.Mark.Val.encCat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:46.555894+00:00
-- url     : https://prove2.me/theorems/842320e7-1b77-4cf0-9ef1-9070d541e164
-- title:
--   Val: enc Cat
-- statement:
--   The codes of the strings of a list of layers, written one after the other, can be read back.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L36-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L36-L45

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
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

theorem PaddedDescent.F.Mark.Val.encCat (hI : StEncInj) (β b : ℕ) (h0 : 0 < b) (hb : b ≤ 2 ^ β) (s s' : ℕ → List Bool) : ∀ l : List ℕ,
    (∀ i ∈ l, (s i).length = (s' i).length) → (l.flatMap fun i => enc β b (s i)) = (l.flatMap fun i => enc β b (s' i)) → ∀ i ∈ l, s i = s' i
  := by sorry
