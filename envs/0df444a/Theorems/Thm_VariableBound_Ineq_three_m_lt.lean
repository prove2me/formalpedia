-- Prove2me | Theorems.Thm_VariableBound_Ineq_three_m_lt
-- name    : VariableBound.Ineq.three_m_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:27.613133+00:00
-- url     : https://prove2.me/theorems/65bae9ba-4c4b-4ca5-a54e-39ad4630cb63
-- title:
--   Ineq: three m lt
-- statement:
--   3m/(n̄+1) < 6Δ·log(2Δ), for 2 ≤ Δ and m ≤ Δ·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L86-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L86-L91

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

theorem VariableBound.Ineq.three_m_lt {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) : 3 * (m : ℝ) / (nb + 1) < 6 * Δ * lg (2 * Δ) := by sorry
