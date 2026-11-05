-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_digit_eq
-- name    : PaddedDescent.F.Mark.Prof.sum_digit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:58.587757+00:00
-- url     : https://prove2.me/theorems/2a9e9dc1-27fe-48e6-826f-f606e867da94
-- title:
--   Prof: sum digit eq
-- statement:
--   Exactly one number below (M+1)^Q has prescribed digits t q ≤ M at the places q < Q, and none if
--   some t q exceeds M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L40-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L40-L50

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

theorem PaddedDescent.F.Mark.Prof.sum_digit_eq (M Q : ℕ) (t : ℕ → ℕ) :
    ∑ y ∈ range ((M + 1) ^ Q), (if ∀ q < Q, digit M y q = t q then (1 : ℤ) else 0) = if ∀ q < Q, t q ≤ M then 1 else 0 := by sorry
