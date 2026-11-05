-- Prove2me | Theorems.Thm_P2M_PaddedDescent_F_Mark_Val___eq_31072c3bb40e
-- name    : P2M_PaddedDescent_F_Mark_Val___eq_31072c3bb40e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:59.244599+00:00
-- url     : https://prove2.me/theorems/9f5aec44-5fbf-4fd0-ad82-bd935830db06
-- title:
--   P2 M Padded Descent F Mark Val   eq 31072c3bb40e: P2 M Padded Descent F Mark Val   eq 31072c3bb40e
-- statement:
--   The interaction of two nodes whose states have the profile is 1 if their strings agree in every
--   layer, and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L244-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L244-L257

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

theorem P2M_PaddedDescent_F_Mark_Val___eq_31072c3bb40e (hLen : StEncLen) (hCat : StEncInj) (h0 : 0 < b) (hb : b ≤ 2 ^ β) {a a' : Fin g} (hne : a ≠ a') {z z' : List Bool}
    (hz : prof g n Ls y a z = true) :
    (markN g (ctx g n β b Ls y)).Ψ a a' z z' =
      if ∀ i < Ls.length, str g n Ls a a' i z = str g n Ls a' a i z' then 1 else 0 := by sorry

alias «PaddedDescent».«F».«Mark».«Val».«Ψ_eq» := P2M_PaddedDescent_F_Mark_Val___eq_31072c3bb40e
