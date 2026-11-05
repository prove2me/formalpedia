-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_range_ite
-- name    : PaddedDescent.F.Mark.Pi.sum_range_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:42:53.154038+00:00
-- url     : https://prove2.me/theorems/2288fa6e-62e9-4dd3-915a-9cfb06c78df5
-- title:
--   Pi: sum range ite
-- statement:
--   A sum over the places below n in which only the place i counts, with c, is c if i < n and 0
--   otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L204-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L204-L210

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.sum_range_ite (n i c : ℕ) : ((List.range n).map fun i' => if i' = i then c else 0).sum = if i < n then c else 0 := by sorry
