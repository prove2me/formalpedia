-- Prove2me | Theorems.Thm_VariableBound_Ineq_nb_mul_le
-- name    : VariableBound.Ineq.nb_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:21.184895+00:00
-- url     : https://prove2.me/theorems/0cc25b5e-64da-4d4e-b9f2-2e2c7f1cadae
-- title:
--   Ineq: nb mul le
-- statement:
--   n̄·log(2Δ) ≤ n, for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L51-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L51-L57

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

theorem VariableBound.Ineq.nb_mul_le {n Δ nb : ℕ} (hΔ : 1 ≤ Δ) (h : IsNb n Δ nb) : (nb : ℝ) * lg (2 * Δ) ≤ n := by sorry
