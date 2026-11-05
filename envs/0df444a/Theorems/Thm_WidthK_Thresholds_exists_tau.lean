-- Prove2me | Theorems.Thm_WidthK_Thresholds_exists_tau
-- name    : WidthK.Thresholds.exists_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:02:40.47096+00:00
-- url     : https://prove2.me/theorems/7ff2381f-db7b-4127-b41e-0b0a0aa061ab
-- title:
--   Thresholds: exists tau
-- statement:
--   For every k, every ε > 0 and every τ₀ there is a number τ ≥ τ₀, τ ≥ 4, with (k/τ)·log₂(e·τ·(2 +
--   β 1 + … + β k)) ≤ ε.
--   The proof takes τ = m² with m ≥ 4·k·(2^(k+1)+1)/ε and uses log m ≤ m − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L196-L243
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean#L196-L243

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

theorem WidthK.Thresholds.exists_tau (k τ₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, τ₀ ≤ τ ∧ 4 ≤ τ ∧
      ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsum τ k : ℝ)) ≤ ε := by sorry
