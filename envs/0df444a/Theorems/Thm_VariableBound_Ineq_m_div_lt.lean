-- Prove2me | Theorems.Thm_VariableBound_Ineq_m_div_lt
-- name    : VariableBound.Ineq.m_div_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:24.70056+00:00
-- url     : https://prove2.me/theorems/3b0c4739-1fd1-4710-8223-35a63dc7d07f
-- title:
--   Ineq: m div lt
-- statement:
--   m/n̄ < 2Δ·log(2Δ), for 2 ≤ Δ and m ≤ Δ·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L77-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L77-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq

theorem VariableBound.Ineq.m_div_lt {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) : (m : ℝ) / nb < 2 * Δ * lg (2 * Δ) := by sorry
