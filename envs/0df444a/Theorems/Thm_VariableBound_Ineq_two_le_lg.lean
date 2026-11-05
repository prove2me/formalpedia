-- Prove2me | Theorems.Thm_VariableBound_Ineq_two_le_lg
-- name    : VariableBound.Ineq.two_le_lg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:38.497514+00:00
-- url     : https://prove2.me/theorems/524564e6-1654-4f03-8d64-879ab68088a3
-- title:
--   Ineq: two le lg
-- statement:
--   log(2Δ) ≥ 2 for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L34-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L34-L39

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

theorem VariableBound.Ineq.two_le_lg {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ lg (2 * Δ) := by sorry
