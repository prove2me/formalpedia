-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_of_le
-- name    : PaddedDescent.F.Mark.Prof.mu_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:22:59.914433+00:00
-- url     : https://prove2.me/theorems/7c4385ba-3a4f-428a-8801-3e79f34e641b
-- title:
--   Prof: mu of le
-- statement:
--   For a ≤ b the profile's number is the digit at the place (a·g + b)·R + i, where R is the number
--   of layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L80-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L80-L82

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

theorem PaddedDescent.F.Mark.Prof.mu_of_le (g : ℕ) (Ls : List Fml) (y : ℕ) {a b : ℕ} (h : a ≤ b) (i : ℕ) :
    mu g Ls y a b i = digit (cls Ls).length y ((a * g + b) * Ls.length + i) := by sorry
