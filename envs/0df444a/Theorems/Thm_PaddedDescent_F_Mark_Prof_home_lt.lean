-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_home_lt
-- name    : PaddedDescent.F.Mark.Prof.home_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:26.180653+00:00
-- url     : https://prove2.me/theorems/98aca799-912e-4571-b60f-5e7c1520bdc6
-- title:
--   Prof: home lt
-- statement:
--   The home of a variable below n is a node below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L110-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L110-L116

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

theorem PaddedDescent.F.Mark.Prof.home_lt {g n x : ℕ} (hg : 0 < g) (hx : x < n) : x / qv g n < g := by sorry
