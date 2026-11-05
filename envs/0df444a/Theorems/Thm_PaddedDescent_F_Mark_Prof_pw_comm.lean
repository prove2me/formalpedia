-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_comm
-- name    : PaddedDescent.F.Mark.Prof.pw_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:23:38.338993+00:00
-- url     : https://prove2.me/theorems/a2a3c991-c812-4200-b6ed-ee92de2a21f1
-- title:
--   Prof: pw comm
-- statement:
--   The number of compared members does not depend on the order of the two nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L85-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L85-L86

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

theorem PaddedDescent.F.Mark.Prof.pw_comm (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : pw g n Ls P a b i = pw g n Ls P b a i := by sorry
