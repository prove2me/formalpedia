-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_place_dec
-- name    : PaddedDescent.F.Mark.Prof.place_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:09:37.470574+00:00
-- url     : https://prove2.me/theorems/99a8994b-4357-4564-8355-174473ab0c01
-- title:
--   Prof: place dec
-- statement:
--   The place (A·g + A')·R + i determines i, A' and A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L53-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L53-L66

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

theorem PaddedDescent.F.Mark.Prof.place_dec {g R A A' i : ℕ} (hA' : A' < g) (hi : i < R) :
    ((A * g + A') * R + i) % R = i ∧ ((A * g + A') * R + i) / R % g = A' ∧ ((A * g + A') * R + i) / R / g = A := by sorry
