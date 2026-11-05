-- Prove2me | Theorems.Thm_VariableBound_Ineq_p_rb
-- name    : VariableBound.Ineq.p_rb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:49.732129+00:00
-- url     : https://prove2.me/theorems/a9c244be-611e-4dff-ae53-04785fa2be1a
-- title:
--   Ineq: p rb
-- statement:
--   p·r̄ < 22·log(2Δ), for 2 ≤ Δ and any number r̄ ≤ 10n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L167-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L167-L175

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

theorem VariableBound.Ineq.p_rb {n Δ nb rb : ℕ} (hΔ : 2 ≤ Δ) (h : IsNb n Δ nb) (hr : rb ≤ 10 * n) : ((pp nb : ℚ) : ℝ) * rb < 22 * lg (2 * Δ) := by sorry
