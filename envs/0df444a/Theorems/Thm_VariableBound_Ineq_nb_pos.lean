-- Prove2me | Theorems.Thm_VariableBound_Ineq_nb_pos
-- name    : VariableBound.Ineq.nb_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:33.535855+00:00
-- url     : https://prove2.me/theorems/6fe7fa54-3af0-4444-a069-f03200e90204
-- title:
--   Ineq: nb pos
-- statement:
--   n̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L72-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L72-L74

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

theorem VariableBound.Ineq.nb_pos {n Δ nb : ℕ} (h : IsNb n Δ nb) : (1 : ℝ) ≤ nb := by sorry
