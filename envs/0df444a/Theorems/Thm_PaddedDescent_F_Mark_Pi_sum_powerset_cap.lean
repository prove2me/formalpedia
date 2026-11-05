-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_cap
-- name    : PaddedDescent.F.Mark.Pi.sum_powerset_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:42:55.019389+00:00
-- url     : https://prove2.me/theorems/f50f35a8-b62b-4b0b-a27d-633df6059780
-- title:
--   Pi: sum powerset cap
-- statement:
--   The sum of s^|P| over the subsets P of S with at most w elements is Σ_{j ≤ w} s^j·C(|S|, j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L127-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L127-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.sum_powerset_cap (S : Finset ι) (w : ℕ) (s : ℤ) :
    ∑ P ∈ S.powerset, (if P.card ≤ w then s ^ P.card else 0) = ∑ j ∈ range (w + 1), s ^ j * (S.card.choose j : ℤ) := by sorry
