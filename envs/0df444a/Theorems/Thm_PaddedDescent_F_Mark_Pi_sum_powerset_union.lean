-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_union
-- name    : PaddedDescent.F.Mark.Pi.sum_powerset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:42:32.512641+00:00
-- url     : https://prove2.me/theorems/63197c77-78ad-4cb2-9918-6bd64028ea5a
-- title:
--   Pi: sum powerset union
-- statement:
--   The sum of F (X ∩ A) · G (X ∩ B) over the subsets X of a disjoint union A ∪ B is the sum of F
--   over the subsets of A times the sum of G over the subsets of B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L36-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L36-L66

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

theorem PaddedDescent.F.Mark.Pi.sum_powerset_union {A B : Finset ι} (hAB : Disjoint A B) (F G : Finset ι → ℤ) :
    ∑ X ∈ (A ∪ B).powerset, F (X ∩ A) * G (X ∩ B) = (∑ P ∈ A.powerset, F P) * ∑ Q ∈ B.powerset, G Q := by sorry
