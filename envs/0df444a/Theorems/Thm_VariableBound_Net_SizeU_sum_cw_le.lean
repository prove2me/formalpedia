-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_sum_cw_le
-- name    : VariableBound.Net.SizeU.sum_cw_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:45:53.868837+00:00
-- url     : https://prove2.me/theorems/cf915883-87b8-4853-9b58-b76e37ed8180
-- title:
--   Size U: sum cw le
-- statement:
--   Step 3, «The total», «Adding two roundings per pair»: for each kind one rounding per pair,
--   Σ_({a,b}) ⌈log C(t_(a,b), μ_(a,b))⌉ ≤ log C(T, μ) + Σ_(b<g) b, and Σ_(b<g) b is the number of pairs;
--   T and μ are the sums of the t_(a,b) and of the μ_(a,b). Needs μ_(a,b) ≤ t_(a,b) for the pairs a < b
--   < g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L206-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L206-L217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.sum_cw_le (g : ℕ) (t μ : ℕ → ℕ → ℕ) (h : ∀ b < g, ∀ a < b, μ a b ≤ t a b) :
    ((∑ b ∈ range g, ∑ a ∈ range b, cw (t a b) (μ a b) : ℕ) : ℝ) ≤
      lg ((∑ b ∈ range g, ∑ a ∈ range b, t a b).choose (∑ b ∈ range g, ∑ a ∈ range b, μ a b)) + (∑ b ∈ range g, b : ℕ) := by sorry
