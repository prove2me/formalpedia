-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_prod_map_eq_prod_range
-- name    : PaddedDescent.F.Mark.Pi.prod_map_eq_prod_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:10.557809+00:00
-- url     : https://prove2.me/theorems/f36401bb-bb5d-44c5-a86e-d4b2f06196a5
-- title:
--   Pi: prod map eq prod range
-- statement:
--   The product of f over a list is the product over its places.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L213-L219
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L213-L219

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.prod_map_eq_prod_range {β : Type*} (f : β → ℤ) (d : β) (l : List β) :
    (l.map f).prod = ∏ i ∈ range l.length, f (l.getD i d) := by sorry
