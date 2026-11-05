-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_term_eq
-- name    : PaddedDescent.F.Mark.Val.term_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:19.053957+00:00
-- url     : https://prove2.me/theorems/c48e7805-5b76-47b8-a0e2-93b39f8ce322
-- title:
--   Val: term eq
-- statement:
--   One term of the value: the product of the signs at a good family of states with the profile, and
--   0 elsewhere.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L605-L636
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L605-L636

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
import Theorems.Thm_Groundwork_SatNet_term_eq

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.term_eq (hLen : StEncLen) (hCat : StEncInj) (h0 : 0 < b) (hb : b ≤ 2 ^ β) (z : Fin g → List Bool) :
    (∏ a, (markN g (ctx g n β b Ls y)).W a (z a)) *
        ∏ p ∈ pairs (Fin g), (markN g (ctx g n β b Ls y)).Ψ p.1 p.2 (z p.1) (z p.2) =
      by classical exact if Gd g n Ls z then
        (if ∀ a : Fin g, prof g n Ls y a (z a) = true then ∏ a : Fin g, (-1 : ℤ) ^ sgE g n Ls a (z a) else 0) else 0 := by sorry
