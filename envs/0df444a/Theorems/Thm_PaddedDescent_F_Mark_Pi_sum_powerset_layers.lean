-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_layers
-- name    : PaddedDescent.F.Mark.Pi.sum_powerset_layers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:10:25.707694+00:00
-- url     : https://prove2.me/theorems/bad0b351-616a-4bf6-acdf-687a38172f70
-- title:
--   Pi: sum powerset layers
-- statement:
--   Let a subset X of V have the weight Π_{i < R} φ i (the part of X in layer i). The sum of the
--   weights is the product over the layers of the sum of φ i over the subsets
--   of layer i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L71-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L71-L123

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

theorem PaddedDescent.F.Mark.Pi.sum_powerset_layers (lay : ι → ℕ) (φ : ℕ → Finset ι → ℤ) (R : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset, ∏ i ∈ range R, φ i (X.filter fun e => lay e = i) =
      ∏ i ∈ range R, ∑ P ∈ (V.filter fun e => lay e = i).powerset, φ i P := by sorry
