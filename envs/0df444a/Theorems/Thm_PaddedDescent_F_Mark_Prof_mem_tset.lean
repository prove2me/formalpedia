-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tset
-- name    : PaddedDescent.F.Mark.Prof.mem_tset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:38:35.112211+00:00
-- url     : https://prove2.me/theorems/041d5710-9e9c-42d9-acaf-8ae1b0ceb4b3
-- title:
--   Prof: mem tset
-- statement:
--   Membership in `tset`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L122-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L122-L123

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
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.mem_tset {g n : ℕ} {Ls : List Fml} {e a : ℕ} : a ∈ tset g n Ls e ↔ a < g ∧ tchB g n Ls a e = true := by sorry
