-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_sum_lg_choose_le
-- name    : VariableBound.Net.SizeU.sum_lg_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:08.995837+00:00
-- url     : https://prove2.me/theorems/231b5903-4383-4fa3-8270-dd344619bcd6
-- title:
--   Size U: sum lg choose le
-- statement:
--   Step 3, «The total»: «A product of binomial coefficients is at most the binomial coefficient of
--   the sums, so Σ_({a,b}) log C(t_(a,b), μ_(a,b)) ≤ log C(T, μ)», where T and μ are the sums of the
--   t_(a,b) and of the
--   μ_(a,b) over the pairs a < b < g. Needs μ_(a,b) ≤ t_(a,b) for these pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L78-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L78-L88

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

theorem VariableBound.Net.SizeU.sum_lg_choose_le (g : ℕ) (t μ : ℕ → ℕ → ℕ) (h : ∀ b < g, ∀ a < b, μ a b ≤ t a b) :
    ∑ b ∈ range g, ∑ a ∈ range b, lg ((t a b).choose (μ a b)) ≤
      lg ((∑ b ∈ range g, ∑ a ∈ range b, t a b).choose (∑ b ∈ range g, ∑ a ∈ range b, μ a b)) := by sorry
