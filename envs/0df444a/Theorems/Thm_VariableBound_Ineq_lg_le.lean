-- Prove2me | Theorems.Thm_VariableBound_Ineq_lg_le
-- name    : VariableBound.Ineq.lg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:23.259932+00:00
-- url     : https://prove2.me/theorems/2dacae91-dc2e-431b-b3e5-293e3738e53a
-- title:
--   Ineq: lg le
-- statement:
--   log(2Δ) ≤ 2Δ for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L42-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L42-L48

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

theorem VariableBound.Ineq.lg_le {Δ : ℕ} (hΔ : 1 ≤ Δ) : lg (2 * Δ) ≤ 2 * Δ := by sorry
