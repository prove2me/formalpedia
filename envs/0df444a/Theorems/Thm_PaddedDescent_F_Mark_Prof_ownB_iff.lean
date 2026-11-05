-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_ownB_iff
-- name    : PaddedDescent.F.Mark.Prof.ownB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:35:37.489224+00:00
-- url     : https://prove2.me/theorems/cf643108-aac6-47a1-8c1b-0a521e8779fc
-- title:
--   Prof: own B iff
-- statement:
--   What `ownB` says: a is touched, and no smaller node is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L152-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L152-L157

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

theorem PaddedDescent.F.Mark.Prof.ownB_iff {g n : ℕ} {Ls : List Fml} {e a : ℕ} :
    ownB g n Ls e a = true ↔ tchB g n Ls a e = true ∧ ∀ c < g, c < a → tchB g n Ls c e = false := by sorry
