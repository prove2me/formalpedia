-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_capped
-- name    : PaddedDescent.F.Mark.Pi.sum_capped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:42:26.963199+00:00
-- url     : https://prove2.me/theorems/9880fe05-8fc6-4bbe-9935-7bbf88334e42
-- title:
--   Pi: sum capped
-- statement:
--   The sum of (−1)^(number of elements outside layer 0) over the subsets X of V with at most w
--   elements in every layer is the product over the layers of the cut-off sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L174-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L174-L189

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

theorem PaddedDescent.F.Mark.Pi.sum_capped (lay : ι → ℕ) (R w : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset.filter (fun X => ∀ i < R, (X.filter fun e => lay e = i).card ≤ w),
        (-1 : ℤ) ^ (X.filter fun e => 1 ≤ lay e).card =
      ∏ i ∈ range R, ∑ j ∈ range (w + 1),
        (if i = 0 then (1 : ℤ) else -1) ^ j * ((V.filter fun e => lay e = i).card.choose j : ℤ) := by sorry
