-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_sum_owner
-- name    : PaddedDescent.F.Mark.Val.sum_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:33.789311+00:00
-- url     : https://prove2.me/theorems/cb7e09fb-9606-423d-9bcf-85f239b0334d
-- title:
--   Val: sum owner
-- statement:
--   Counting the clauses of P with a property p owner by owner counts each once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L381-L395
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L381-L395

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.sum_owner (hg : 0 < g) (hW : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ Finset.range (cls Ls).length) (p : ℕ → Prop) [DecidablePred p] :
    ∑ a ∈ Finset.range g, (P.filter fun e => p e ∧ ownB g n Ls e a = true).card = (P.filter p).card := by sorry
