-- Prove2me | Theorems.Thm_VariableBound_Ineq_six_le
-- name    : VariableBound.Ineq.six_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:35.15949+00:00
-- url     : https://prove2.me/theorems/c0b5fc9a-def9-4197-a7c1-fa7a33d771d3
-- title:
--   Ineq: six le
-- statement:
--   6Δ·log(2Δ) ≤ (2Δ)³, for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L94-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L94-L98

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

theorem VariableBound.Ineq.six_le {Δ : ℕ} (hΔ : 2 ≤ Δ) : 6 * (Δ : ℝ) * lg (2 * Δ) ≤ (2 * Δ) ^ 3 := by sorry
