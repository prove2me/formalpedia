-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_prod_sign
-- name    : PaddedDescent.F.Mark.Pi.prod_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:10:28.579043+00:00
-- url     : https://prove2.me/theorems/d8f94dcc-a748-4761-a521-5e0df99b8130
-- title:
--   Pi: prod sign
-- statement:
--   With the factor 1 for each element of layer 0 and −1 for each other element, the product over
--   the layers is (−1)^(number of elements outside layer 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L151-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L151-L170

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.prod_sign (lay : ι → ℕ) (R : ℕ) (X : Finset ι) (hX : ∀ e ∈ X, lay e < R) :
    ∏ i ∈ range R, (if i = 0 then (1 : ℤ) else -1) ^ (X.filter fun e => lay e = i).card =
      (-1) ^ (X.filter fun e => 1 ≤ lay e).card := by sorry
