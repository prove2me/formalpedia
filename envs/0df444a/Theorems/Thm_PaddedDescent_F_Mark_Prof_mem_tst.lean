-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst
-- name    : PaddedDescent.F.Mark.Prof.mem_tst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:38:11.442863+00:00
-- url     : https://prove2.me/theorems/a1f9d292-17ab-4b0a-abd5-c52396e226c7
-- title:
--   Prof: mem tst
-- statement:
--   Membership in `tst` for a' < a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L253-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L253-L256

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.mem_tst {g n : ℕ} {Ls : List Fml} {a' a i e : ℕ} (hlt : a' < a) :
    e ∈ tst g n Ls a' a i ↔ e < (cls Ls).length ∧ (clAt Ls e).1 = i ∧ linkB g n Ls e a' a = true := by sorry
