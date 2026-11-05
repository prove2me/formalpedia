-- Prove2me | Theorems.Thm_VariableBound_Ineq_lt_nb_mul
-- name    : VariableBound.Ineq.lt_nb_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:16.134105+00:00
-- url     : https://prove2.me/theorems/6efbd465-3135-4ead-acf9-9bd9056f78cd
-- title:
--   Ineq: lt nb mul
-- statement:
--   n < 2·n̄·log(2Δ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L60-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L60-L65

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

theorem VariableBound.Ineq.lt_nb_mul {n Δ nb : ℕ} (h : IsNb n Δ nb) : (n : ℝ) < 2 * nb * lg (2 * Δ) := by sorry
