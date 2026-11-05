-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
-- name    : PaddedDescent.F.Mark.Prof.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:13:32.581763+00:00
-- url     : https://prove2.me/theorems/4379dc6a-0d2a-4921-a5a1-56d107059433
-- title:
--   Prof: link B iff
-- statement:
--   What `linkB` says: a < b are touched, and no node between them is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L160-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L160-L170

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
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.linkB_iff {g n : ℕ} {Ls : List Fml} {e a b : ℕ} :
    linkB g n Ls e a b = true ↔ a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧
      ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by sorry
