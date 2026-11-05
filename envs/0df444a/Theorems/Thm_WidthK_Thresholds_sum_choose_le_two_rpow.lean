-- Prove2me | Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
-- name    : WidthK.Thresholds.sum_choose_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:36:40.027667+00:00
-- url     : https://prove2.me/theorems/627252ce-c0a9-42aa-872d-92caf896b180
-- title:
--   Thresholds: sum choose le two rpow
-- statement:
--   If (k/τ)·log₂(e·τ·L) ≤ ε, with k ≤ L and 1 ≤ τ, then Σ_{j ≤ kn/τ} C(L·n, j) ≤ 2^(εn).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L136-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L136-L191

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SparsifyWidthK_Thresholds
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
open Groundwork.Sparsify

theorem WidthK.Thresholds.sum_choose_le_two_rpow {k τ L : ℕ} (hτ : 1 ≤ τ) (hkL : k ≤ L) {ε : ℝ}
    (h : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) ≤ ε) (n : ℕ) :
    ((∑ j ∈ range (k * n / τ + 1), (L * n).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by sorry
